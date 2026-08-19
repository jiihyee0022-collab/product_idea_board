import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';
import { createWorker } from 'tesseract.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
try { process.loadEnvFile(path.join(__dirname, '.env')); } catch (e) { /* no .env file — fine in production (Render), where config comes from real env vars */ }

const publicPath = path.join(__dirname, 'public');
const port = process.env.PORT || 8080;

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.ico': 'image/x-icon'
};

const MAX_LINKS = 10;
const FETCH_TIMEOUT_MS = 12000;
const MAX_BODY_BYTES = 20000;

function sendJson(res, status, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Content-Length': Buffer.byteLength(body) });
  res.end(body);
}

function decodeEntities(str) {
  return str
    .replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"').replace(/&#39;/g, "'").replace(/&nbsp;/g, ' ');
}

function stripTags(html) {
  return decodeEntities(
    html
      .replace(/<script[\s\S]*?<\/script>/gi, ' ')
      .replace(/<style[\s\S]*?<\/style>/gi, ' ')
      .replace(/<[^>]+>/g, ' ')
  ).replace(/\s+/g, ' ').trim();
}

function firstMatch(re, source) {
  const m = source.match(re);
  return m ? decodeEntities(m[1].trim()) : null;
}

function extractBasicMeta(html) {
  const head = (html.match(/<head[^>]*>([\s\S]*?)<\/head>/i) || [null, html.slice(0, 50000)])[1];
  function metaContent(propOrName, key) {
    return (
      firstMatch(new RegExp('<meta[^>]+' + key + '=["\']' + propOrName + '["\'][^>]+content=["\']([^"\']*)["\']', 'i'), head) ||
      firstMatch(new RegExp('<meta[^>]+content=["\']([^"\']*)["\'][^>]+' + key + '=["\']' + propOrName + '["\']', 'i'), head)
    );
  }
  const titleTag = firstMatch(/<title[^>]*>([^<]*)<\/title>/i, head);
  const ogTitle = metaContent('og:title', 'property');
  const ogImage = metaContent('og:image', 'property');
  const ogDesc = metaContent('og:description', 'property');
  const metaDesc = metaContent('description', 'name');
  return { title: ogTitle || titleTag || null, image: ogImage || null, description: ogDesc || metaDesc || null };
}

// ---------- price extraction ----------
function extractPrice(html, bodyText) {
  const structuredPatterns = [
    /<meta[^>]+property=["']product:price:amount["'][^>]+content=["']([\d,.]+)["']/i,
    /<meta[^>]+itemprop=["']price["'][^>]+content=["']([\d,.]+)["']/i,
    /"salePrice"\s*:\s*"?([\d]{3,10})"?/i,
    /"price"\s*:\s*"?([\d]{3,10})"?/i
  ];
  for (const re of structuredPatterns) {
    const m = html.match(re);
    if (m) {
      const n = Number(m[1].replace(/,/g, ''));
      if (n > 0) return n;
    }
  }
  // fallback: most frequently repeated ₩/원 price-looking number in visible text
  const matches = [
    ...bodyText.matchAll(/(?:₩\s?)([\d]{1,3}(?:,\d{3})+|\d{4,7})(?!\d)/g),
    ...bodyText.matchAll(/([\d]{1,3}(?:,\d{3})+|\d{4,7})\s?원(?!\w)/g)
  ];
  if (!matches.length) return null;
  const counts = {};
  matches.forEach((m) => {
    const v = m[1].replace(/,/g, '');
    counts[v] = (counts[v] || 0) + 1;
  });
  const sorted = Object.entries(counts).sort((a, b) => b[1] - a[1]);
  return Number(sorted[0][0]);
}

// ---------- weight / volume extraction ----------
const UNIT_RE = /(\d+(?:\.\d+)?)\s?(kg|킬로그램|킬로|g|그램|그람|ml|밀리리터|㎖|l|리터)(?![a-zA-Z가-힣])/gi;
function weightMatchCounts(text) {
  const matches = [...text.matchAll(UNIT_RE)];
  const counts = {};
  matches.forEach((m) => {
    const num = parseFloat(m[1]);
    const unit = m[2].toLowerCase();
    let grams = null;
    let ml = null;
    if (/^(kg|킬로그램|킬로)$/.test(unit)) grams = num * 1000;
    else if (/^(g|그램|그람)$/.test(unit)) grams = num;
    else if (/^(l|리터)$/.test(unit)) ml = num * 1000;
    else if (/^(ml|밀리리터|㎖)$/.test(unit)) ml = num;
    if (grams == null && ml == null) return;
    // sanity cap — real consumer products are rarely heavier/larger than 50kg / 50L;
    // beyond that it's almost certainly an unrelated number on the page (dates, counts, etc.)
    if ((grams != null && grams > 50000) || (ml != null && ml > 50000)) return;
    const key = grams != null ? `g:${grams}` : `ml:${ml}`;
    counts[key] = (counts[key] || 0) + 1;
  });
  return counts;
}
function pickWeight(counts) {
  const entries = Object.entries(counts);
  if (!entries.length) return null;
  const sorted = entries.sort((a, b) => b[1] - a[1]);
  const [kind, amountStr] = sorted[0][0].split(':');
  const amount = Number(amountStr);
  if (!amount) return null;
  return { type: kind === 'g' ? 'weight' : 'volume', amount, unit: kind === 'g' ? 'g' : 'ml' };
}
function extractWeight(bodyText, titleText) {
  // Prefer whatever unit mention appears in the product title — sellers almost always put
  // the net weight there, and it's far more reliable than "most frequent in the whole page"
  // (related-product carousels, bundled gifts, etc. can outnumber the real one in body text).
  if (titleText) {
    const fromTitle = pickWeight(weightMatchCounts(titleText));
    if (fromTitle) return fromTitle;
  }
  return pickWeight(weightMatchCounts(bodyText));
}

function computeUnitPrice(price, weight) {
  if (!price || !weight || !weight.amount) return null;
  const per100 = (price / weight.amount) * 100;
  return { amount: Math.round(per100), unit: weight.unit === 'g' ? '100g' : '100ml' };
}

// ---------- review keyword spotting: semantic "attribute + evaluation" units ----------
// A bare sentiment word ('좋아요', '별로예요') carries no product information on its own —
// only meaningful once paired with the attribute it's evaluating ("세정력이 좋아요" -> 세정력 만족).
// Each concept below is a regex over (attribute-noun ... evaluation-word) within a short window,
// so "세정력이 정말 좋아요"/"세정력 좋네요"/"세정력은 만족스러워요" all collapse to one canonical label —
// never the raw conjugated phrase, and never a standalone emotion word with no attribute attached.
const POSITIVE_CONCEPTS = [
  { label: '악취 제거 효과', re: /(냄새|악취|꿉꿉)[\s\S]{0,12}(없어지|사라지|안\s?나|잡히|제거|개선|줄어)/ },
  { label: '세정력 만족', re: /(세정력|세척력|클렌징력)[\s\S]{0,10}(좋|만족|훌륭|괜찮|최고|탁월)/ },
  { label: '탈취력 만족', re: /(탈취력|탈취효과)[\s\S]{0,10}(좋|만족|훌륭|괜찮|최고|탁월|확실|있는것|있어요|있습니다)/ },
  { label: '제습력 만족', re: /(제습력|습기\s?제거)[\s\S]{0,10}(좋|만족|훌륭|괜찮|최고|탁월|확실)/ },
  { label: '무향', re: /무향/ },
  { label: '향 만족', re: /향[\s\S]{0,8}(좋|은은|고급|맘에\s?들)/ },
  { label: '사용 편의성', re: /(쓰기|사용하기|사용)[\s\S]{0,8}(편하|편리|쉬워|간편)/ },
  { label: '넉넉한 용량', re: /(양|용량|사이즈|크기)[\s\S]{0,8}(많|넉넉|큼|크|충분)/ },
  { label: '가성비 만족', re: /(가격|가성비)[\s\S]{0,8}(좋|만족|착함|합리적|저렴)/ },
  { label: '빠른 배송', re: /배송[\s\S]{0,8}(빠르|신속|좋)/ },
  { label: '튼튼한 내구성', re: /(내구성|튼튼)[\s\S]{0,8}(좋|튼튼|단단)/ },
  { label: '예쁜 디자인', re: /디자인[\s\S]{0,8}(예쁘|이쁘|고급스럽|세련|만족)/ },
  { label: '재구매 의사', re: /재구매|다시\s?구매|또\s?구매|재주문|추가\s?구매/ },
  { label: '지속력 만족', re: /지속(력|시간)[\s\S]{0,8}(좋|길|오래)/ },
  { label: '가벼운 무게', re: /(무게|중량)[\s\S]{0,8}(가볍|경량)/ },
  { label: '간편한 휴대', re: /휴대[\s\S]{0,8}(편하|간편|좋)/ },
  { label: '꼼꼼한 포장', re: /포장[\s\S]{0,8}(꼼꼼|안전|튼튼|좋)/ },
  { label: '효과 체감', re: /효과[\s\S]{0,8}(있|확실|좋)/ }
];
const NEGATIVE_CONCEPTS = [
  // "효과가 있는지 잘 모르겠어요" / "효과가 없어졌어요" — both land here.
  { label: '효과 체감 부족', re: /효과[\s\S]{0,10}(없|모르겠|약하|미미|체감\s?안)/ },
  // "처음에는 좋았는데 금방 효과가 없어졌어요" — time-based degradation, distinct from a flat "no effect".
  { label: '지속력 부족', re: /(금방|빨리|처음)[\s\S]{0,10}(효과|없어지|없어져|약해지|끝나)/ },
  // "생각보다 빨리 없어져요" — 없어지다 conjugates to 없어져(요), which does NOT contain the substring
  // "없어지"; matching only the dictionary form silently missed the single most common phrasing.
  { label: '짧은 사용기간', re: /(금방|빨리|얼마\s?안|일찍)[\s\S]{0,8}(없어지|없어져|끝나|다\s?써|소진)/ },
  // "조금 비싼 것 같아요" has no explicit "가격" noun at all — bare 비싸(다) is unambiguous on its own,
  // so it's included as a standalone alternative, not only as an attribute+eval pair.
  { label: '가격 부담', re: /가격[\s\S]{0,10}(비싸|높|부담|조정.{0,6}필요|인상|재검토)|비싸|비쌈/ },
  { label: '누액 문제', re: /(액체|물|내용물|용액)[\s\S]{0,8}(새|샘|누출|흘러)|새서|샜/ },
  // "포장 파손"/"박스 파손" style AND bare "파손"/"깨짐" alone (a review rarely bothers naming the box).
  { label: '포장 파손', re: /(포장|박스|용기)[\s\S]{0,8}(파손|찢어|깨져|망가)|파손|깨짐|깨졌/ },
  { label: '배송 지연', re: /배송[\s\S]{0,8}(늦|지연|오래)/ },
  { label: '강한 향', re: /향[\s\S]{0,8}(너무\s?강|진하|독하)/ },
  { label: '향 부족/자극', re: /(향|냄새)[\s\S]{0,8}(약하|안\s?좋|불쾌|자극)/ },
  // "냄새가 난다/나요" is negative — but "안나요" ("no smell") is the '무향' POSITIVE case, so the
  // tempered-dot gap `(?:(?!안|않)[\s\S])` forbids "안"/"않" from appearing in between the two.
  // "않" (안 + 다 contraction, e.g. "냄새가 않나요") is an extremely common real-world spelling
  // variant/typo for the same negation and was previously missed, flipping positive reviews negative.
  { label: '악취 지속', re: /(냄새|악취)(?:(?!안|않)[\s\S]){0,8}(난다|나요|나네요|심하|여전|그대로|계속\s?나)/ },
  { label: '세정력 부족', re: /(세정력|세척력)[\s\S]{0,8}(별로|약하|부족|안\s?좋)/ },
  { label: '탈취력 부족', re: /(탈취력|탈취효과)[\s\S]{0,8}(별로|약하|부족|안\s?좋|없)/ },
  { label: '내구성 부족', re: /(내구성|튼튼)[\s\S]{0,8}(약하|부실|헐겁)/ },
  { label: '재구매 의사 없음', re: /재구매\s?안|다시\s?안\s?살|재구매\s?의사\s?없|또\s?안\s?살/ },
  { label: '기대 이하', re: /기대\s?이하|기대\s?보다|생각보다\s?별로/ },
  { label: '환불 요청', re: /환불[\s\S]{0,6}(요청|받|했)/ },
  { label: '불량품', re: /불량/ },
  { label: '적은 용량', re: /(양|용량)[\s\S]{0,8}(적|부족|작)/ },
  { label: '사용 불편', re: /(사용|쓰기)[\s\S]{0,8}(불편|어렵|힘들|번거)/ },
  { label: '이물질 발견', re: /이물질/ }
];

// A bare emotion word with NO linked attribute still carries real signal — dropping it entirely
// throws away a genuine opinion just because it's short ("적극 추천", "만족합니다"). Used only when
// a review matches none of the attribute-linked concepts above — a specific attribute match always
// wins over these ("가격이 비싸서 아쉬워요" -> 가격 부담, never 전반적 아쉬움).
const GENERIC_POSITIVE_WORDS = ['좋아요', '좋습니다', '좋네요', '만족', '추천', '최고', '괜찮', '훌륭'];
// Split into two buckets (matching the positive side's single-bucket shape but mirrored to what
// Korean actually distinguishes): flat dissatisfaction vs. regret/wistfulness read differently even
// though both are negative, so they get distinct fallback labels — '별로예요' -> 전반적 불만,
// '아쉬워요' -> 전반적 아쉬움 — dissatisfaction words checked first since they're the stronger signal.
const GENERIC_NEGATIVE_DISSATISFIED_WORDS = ['별로', '실망', '최악', '불만', '안돼요', '안된다', '안됨', '기대이하'];
const GENERIC_NEGATIVE_REGRET_WORDS = ['아쉽', '아쉬워'];

// Small samples deserve a lower bar: a single genuine mention in an 11-review batch is real signal,
// not noise — requiring the same count threshold regardless of sample size would silently erase it.
function minFrequencyFor(totalReviews) {
  if (totalReviews < 30) return 1;
  if (totalReviews < 100) return 2;
  return 3;
}

// Korean review lists are almost always timestamped per entry (2026.08.19 / 2026-08-19),
// so splitting on that date pattern approximates individual review boundaries without
// needing site-specific DOM structure — lets us count "N reviews mention X", not raw hits.
function splitIntoReviewChunks(bodyText) {
  const DATE_RE = /\d{4}[.\-]\s?\d{1,2}[.\-]\s?\d{1,2}/g;
  const marks = [...bodyText.matchAll(DATE_RE)].map((m) => m.index);
  if (marks.length < 2) return [bodyText];
  const chunks = [];
  for (let i = 0; i < marks.length; i++) {
    const start = marks[i];
    const end = i + 1 < marks.length ? marks[i + 1] : bodyText.length;
    chunks.push(bodyText.slice(start, end));
  }
  return chunks;
}


// ---------- shared browser (Playwright) ----------
// A single shared instance, with uses queued one at a time — headless Chromium is heavy, and
// running several concurrently would risk exhausting memory on a small host.
let browserPromise = null;
function getBrowser() {
  if (!browserPromise) {
    browserPromise = chromium.launch({
      headless: true,
      // Low-memory-container flags — matters on hosts like Render's free tier (512MB total),
      // where a default Chromium launch can push the whole process over the limit by itself.
      args: ['--disable-dev-shm-usage', '--disable-gpu', '--no-zygote', '--disable-software-rasterizer', '--disable-extensions']
    });
  }
  return browserPromise;
}
let playwrightQueue = Promise.resolve();
function runExclusive(fn) {
  const run = playwrightQueue.then(fn, fn);
  playwrightQueue = run.then(() => {}, () => {});
  return run;
}
const DEFAULT_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36';

// ---------- generic static-HTML review detection (fallback path, no adapter matched) ----------
// Real review lists are timestamped per entry, so a DENSE run of nearby dates is strong,
// site-agnostic evidence of "this is the review list" — unlike anchoring on a heading string,
// which can appear once in an unrelated nav/footer context and point us at the wrong text.
const DATE_RE_G = /\d{4}[.\-]\s?\d{1,2}[.\-]\s?\d{1,2}/g;
const REVIEW_CLUSTER_GAP_MAX = 800; // max chars between consecutive dated entries to count as one list
const REVIEW_CLUSTER_MIN_COUNT = 3; // need at least this many clustered dates to call it "reviews"

function findReviewClusterSpan(bodyText) {
  const positions = [...bodyText.matchAll(DATE_RE_G)].map((m) => m.index);
  if (positions.length < REVIEW_CLUSTER_MIN_COUNT) return null;
  let bestStart = positions[0], bestEnd = positions[0], bestCount = 1;
  let curStart = positions[0], curEnd = positions[0], curCount = 1;
  for (let i = 1; i < positions.length; i++) {
    if (positions[i] - positions[i - 1] <= REVIEW_CLUSTER_GAP_MAX) {
      curEnd = positions[i];
      curCount++;
    } else {
      if (curCount > bestCount) { bestCount = curCount; bestStart = curStart; bestEnd = curEnd; }
      curStart = positions[i]; curEnd = positions[i]; curCount = 1;
    }
  }
  if (curCount > bestCount) { bestCount = curCount; bestStart = curStart; bestEnd = curEnd; }
  if (bestCount < REVIEW_CLUSTER_MIN_COUNT) return null;
  return { start: bestStart, end: Math.min(bodyText.length, bestEnd + 500), count: bestCount };
}

// Sites often print a review board's own stated total near its heading, e.g. "상품후기 (227)" —
// distinct from how many of those we actually manage to fetch. Several smaller numbers can
// appear near review-labeled text too (a "photo reviews: 20" sub-section, a Q&A count, a
// DIFFERENT narrower widget's own subtotal, etc.) so take the largest candidate, never the first.
function findStatedReviewCount(html) {
  const matches = [...html.matchAll(/(?:상품후기|상품평|상품\s?사용후기|이용후기|구매후기|고객리뷰|리뷰)\s*[\(\[]?\s*(\d{1,6})\s*[\)\]]?/g)];
  if (!matches.length) return null;
  return Math.max(...matches.map((m) => Number(m[1])));
}

// A visible "다음 페이지" / numbered page list / fragment-paginated `page_N=` link means there's
// more review content than whatever we found on this single static load.
function hasMoreReviewPagesHint(html, bodyText) {
  if (/다음\s?페이지|다음\s?글|next\s?page/i.test(bodyText)) return true;
  if (/page_\d+=[2-9]/i.test(html)) return true;
  if (/(?:페이지|page)\D{0,3}1\D{0,3}2\D{0,3}3/.test(bodyText)) return true;
  return false;
}

function detectIframes(html) {
  const srcs = [...html.matchAll(/<iframe[^>]+src=["']([^"']+)["']/gi)].map((m) => m[1]);
  return srcs.some((s) => /review|board|comment/i.test(s));
}

const REVIEW_TAB_LABELS = ['상품후기', '상품 사용후기', '구매후기', '이용후기', 'REVIEW', 'Review'];
const NEXT_PAGE_LABELS = ['다음 페이지', '다음', 'Next'];
const MAX_PAGINATION_CLICKS = 4; // up to 5 pages total (first load + 4 clicks) — bounds worst-case latency

// Waits for the review AREA's own content to actually change, instead of a blind fixed sleep —
// records a snapshot of the visible text before clicking "next", clicks, then polls (bounded)
// until that snapshot differs. Falls back to "clicked but couldn't confirm a change" on timeout,
// which the caller treats as "stop paginating", not as a fatal error.
async function clickNextAndWaitForChange(page) {
  const before = await page.evaluate(() => document.body.innerText.slice(0, 800));
  let clicked = false;
  for (const label of NEXT_PAGE_LABELS) {
    try {
      // .last() — pagination controls sit at the bottom of a review list; an early match for
      // generic text like "다음" is more likely to be an unrelated banner/carousel button
      const locator = page.getByText(label, { exact: false }).last();
      if (await locator.count() > 0) {
        await locator.click({ timeout: 2000 });
        clicked = true;
        break;
      }
    } catch (e) { /* this label not present/clickable — try the next one */ }
  }
  if (!clicked) return false;
  try {
    await page.waitForFunction(
      (prev) => document.body.innerText.slice(0, 800) !== prev,
      before,
      { timeout: 6000, polling: 200 }
    );
  } catch (e) {
    // no detectable change within budget — likely means this WAS the last page; stop cleanly
    return false;
  }
  return true;
}

// Generic DOM fallback: click the review tab, scroll it into view, then page through using
// content-change detection (not fixed timeouts) — used only when no adapter recognizes the site.
async function renderAndPaginateReviews(url) {
  return runExclusive(async () => {
    const browser = await getBrowser();
    const context = await browser.newContext({ userAgent: DEFAULT_UA, locale: 'ko-KR' });
    const page = await context.newPage();
    try {
      try {
        await page.goto(url, { waitUntil: 'networkidle', timeout: 20000 });
      } catch (e) {
        // some pages keep a connection open (polling/analytics) and never reach networkidle —
        // that's fine, we still got the DOM; just proceed without treating it as fatal.
      }
      await page.waitForTimeout(3000);
      for (const label of REVIEW_TAB_LABELS) {
        try {
          const locator = page.getByText(label, { exact: false }).first();
          if (await locator.count() > 0) {
            await locator.scrollIntoViewIfNeeded({ timeout: 2000 }).catch(() => {});
            await locator.click({ timeout: 2000 });
            await page.waitForTimeout(1200);
            break;
          }
        } catch (e) { /* tab not present/clickable — fine, keep going */ }
      }
      for (let i = 0; i < 4; i++) {
        try { await page.evaluate(() => window.scrollBy(0, document.body.scrollHeight / 4)); } catch (e) { /* ignore */ }
        await page.waitForTimeout(500);
      }

      let combinedHtml = await page.content();
      for (let click = 0; click < MAX_PAGINATION_CLICKS; click++) {
        const advanced = await clickNextAndWaitForChange(page);
        if (!advanced) break;
        combinedHtml += ' ' + (await page.content());
      }
      return combinedHtml;
    } finally {
      await page.close().catch(() => {});
      await context.close().catch(() => {});
    }
  });
}

// ================= site adapters =================
// Different platforms/widgets expose reviews differently. Each adapter (a) detects whether it
// applies to this page and (b) if so, returns reviews already split one-per-item — no date-cluster
// guessing needed, because a structured API tells us exactly where one review ends and the next
// begins. Adapters are tried in order; the first one that returns actual content wins.

// Adapter: Alpha Review widget (review-widget.alphwidget.com) — a common 3rd-party Cafe24 review
// app. Its data never appears in static HTML (even the widget_code is resolved client-side), so we
// sniff ITS OWN network calls during one real render, then call the review API directly afterward —
// no more browser needed once we know product_no + widget_code.
async function discoverAlphaReviewWidget(rawUrl) {
  return runExclusive(async () => {
    const browser = await getBrowser();
    const context = await browser.newContext({ userAgent: DEFAULT_UA, locale: 'ko-KR' });
    const page = await context.newPage();
    const captured = [];
    page.on('response', async (res) => {
      const u = res.url();
      if (!u.includes('review-widget.alphwidget.com')) return;
      const ct = res.headers()['content-type'] || '';
      if (!ct.includes('json')) return;
      try { captured.push({ url: u, json: await res.json() }); } catch (e) { /* non-JSON or empty body */ }
    });
    try {
      try { await page.goto(rawUrl, { waitUntil: 'networkidle', timeout: 20000 }); } catch (e) { /* proceed anyway */ }
      await page.waitForTimeout(3000);
      // A wider "full review list" sub-widget can init noticeably later than a narrower "photo
      // carousel" sub-widget above the fold — clicking the review tab is unreliable (overlay
      // banners intercept it) and, empirically, isn't actually what triggers it; what matters is
      // giving the page enough total elapsed time while repeatedly scrolling. Poll the captured
      // responses themselves and stop early once a `/meta` call reports a total_count we haven't
      // already seen, instead of guessing a fixed duration.
      // Different sub-widgets on the same page load on their own independent schedule (a photo
      // carousel above the fold can fire well before the full review-list widget lower down), so
      // stopping as soon as ONE candidate appears and stays unchanged for a few rounds is unsafe —
      // a bigger one can still be about to fire. Always run the full budget; the extra few seconds
      // buys real correctness (right widget_code) instead of settling for the first one seen.
      for (let i = 0; i < 14; i++) {
        try { await page.evaluate(() => window.scrollBy(0, document.body.scrollHeight / 6)); } catch (e) { /* ignore */ }
        await page.waitForTimeout(900);
      }
    } finally {
      await page.close().catch(() => {});
      await context.close().catch(() => {});
    }
    return captured;
  });
}

// The widget set can include several sub-widgets (photo-only carousel, rating summary, notice,
// full board) — the one with the LARGEST reported total_count is the full review list; narrower
// ones (e.g. a "photo reviews only" carousel) report a smaller subset of the same product.
function pickFullReviewWidget(captured) {
  let best = null;
  captured.forEach((c) => {
    if (!c.url.includes('/api-widget/meta')) return;
    const totalCount = c.json && c.json.total_count;
    if (typeof totalCount !== 'number') return;
    if (!best || totalCount > best.totalCount) {
      const u = new URL(c.url);
      // the widget dictates its own page size (seen as low as 5) — the API silently ignores
      // whatever page_size we ask for and returns its configured amount regardless, so we must
      // paginate using THIS number, not assume a client-chosen one will be honored.
      const pageSize = Number(u.searchParams.get('page_size')) || 10;
      best = { totalCount, widgetCode: u.searchParams.get('widget_code'), productNo: u.searchParams.get('product_no'), pageSize };
    }
  });
  return best;
}

const ALPHA_REVIEW_MAX = 50;
const ALPHA_REVIEW_MAX_PAGES = 20; // safety cap independent of page size (e.g. 5/page x 20 = 100 attempts max)

async function alphaReviewAdapter(rawUrl, html) {
  if (!html.includes('alphwidget')) return null; // this adapter doesn't apply to this page at all

  const captured = await discoverAlphaReviewWidget(rawUrl);
  const target = pickFullReviewWidget(captured);
  if (!target || !target.widgetCode || !target.productNo) {
    return {
      chunks: [],
      diagnostics: {
        review_count_displayed: null, review_items_collected: 0, review_source: 'none',
        review_api_url: null, iframe_detected: detectIframes(html), pagination_type: 'none',
        failure_reason: 'alpha review widget detected but no widget_code could be resolved from network traffic'
      }
    };
  }

  const seenIds = new Set();
  const reviewObjs = [];
  let lastApiUrl = null;
  for (let page = 1; page <= ALPHA_REVIEW_MAX_PAGES && reviewObjs.length < ALPHA_REVIEW_MAX; page++) {
    const apiUrl = `https://review-widget.alphwidget.com/v2/api-widget?page=${page}&page_size=${target.pageSize}&sort=-created_at&media_only=false&product_no=${target.productNo}&widget_code=${target.widgetCode}&device=w`;
    lastApiUrl = apiUrl;
    let batch = null;
    try {
      const res = await fetch(apiUrl, { headers: { 'User-Agent': DEFAULT_UA, 'Accept': 'application/json' } });
      if (res.ok) batch = await res.json();
    } catch (e) { break; } // network error — stop, keep whatever we already have
    if (!Array.isArray(batch) || batch.length === 0) break; // last page reached

    let newInThisBatch = 0;
    for (const r of batch) {
      if (r.id != null && seenIds.has(r.id)) continue; // duplicate review_id — end of the list
      if (r.id != null) seenIds.add(r.id);
      reviewObjs.push(r);
      newInThisBatch++;
      if (reviewObjs.length >= ALPHA_REVIEW_MAX) break;
    }
    if (newInThisBatch === 0) break; // every id in this batch was already seen — stop
    if (batch.length < target.pageSize) break; // short batch — this was the last page
    await sleep(250); // stay polite between paginated requests
  }

  if (reviewObjs.length === 0) {
    return {
      chunks: [],
      diagnostics: {
        review_count_displayed: target.totalCount, review_items_collected: 0, review_source: 'none',
        review_api_url: lastApiUrl, iframe_detected: false, pagination_type: 'api_page',
        failure_reason: 'widget_code resolved but the review API returned no items'
      }
    };
  }

  const chunks = reviewObjs.map((r) => String(r.content || '')).filter(Boolean);
  // ratings is an AUXILIARY cross-check only (logged, never used to invent a keyword the review
  // text itself doesn't support) — the API happens to expose a 1-5 star field per review.
  const ratings = reviewObjs.map((r) => (typeof r.ratings === 'number' ? r.ratings : null));
  return {
    chunks,
    ratings,
    diagnostics: {
      review_count_displayed: target.totalCount, review_items_collected: chunks.length, review_source: 'xhr_api',
      review_api_url: `https://review-widget.alphwidget.com/v2/api-widget?widget_code=${target.widgetCode}&product_no=${target.productNo}`,
      iframe_detected: false, pagination_type: 'api_page', failure_reason: null
    }
  };
}

const REVIEW_ADAPTERS = [alphaReviewAdapter];

// ================= orchestration =================
// 1) Try each known adapter (structured API — most reliable, per adapter).
// 2) Static inline snapshot, IF nothing suggests it's a partial first page.
// 3) Playwright: click through the real UI with change-detection waits (not fixed timeouts).
// 4) Generic review-board link as an absolute last resort (a board_no like `4` is sometimes a
//    site-wide board mixing in other products, so it's the least trustworthy source).
async function collectReviewData(rawUrl, html) {
  for (const adapter of REVIEW_ADAPTERS) {
    let result = null;
    try { result = await adapter(rawUrl, html); } catch (e) { /* this adapter failed — try the next signal */ }
    if (result) return result; // adapter recognized the site, whether or not it found reviews
  }

  const bodyText = stripTags(html);
  const statedTotal = findStatedReviewCount(html);
  const inlineCluster = findReviewClusterSpan(bodyText);
  const morePagesHint = hasMoreReviewPagesHint(html, bodyText);
  const iframeDetected = detectIframes(html);

  if (inlineCluster && !morePagesHint) {
    const text = bodyText.slice(inlineCluster.start, inlineCluster.end);
    return {
      chunks: splitIntoReviewChunks(text),
      diagnostics: {
        review_count_displayed: statedTotal != null ? statedTotal : inlineCluster.count, review_items_collected: inlineCluster.count,
        review_source: 'inline', review_api_url: null, iframe_detected: iframeDetected, pagination_type: 'none', failure_reason: null
      }
    };
  }

  try {
    const renderedHtml = await renderAndPaginateReviews(rawUrl);
    const renderedBodyText = stripTags(renderedHtml);
    const renderedCluster = findReviewClusterSpan(renderedBodyText);
    if (renderedCluster) {
      const renderedStatedTotal = findStatedReviewCount(renderedHtml);
      const text = renderedBodyText.slice(renderedCluster.start, renderedCluster.end);
      return {
        chunks: splitIntoReviewChunks(text),
        diagnostics: {
          review_count_displayed: renderedStatedTotal != null ? renderedStatedTotal : (statedTotal != null ? statedTotal : renderedCluster.count),
          review_items_collected: renderedCluster.count, review_source: 'inline', review_api_url: null,
          iframe_detected: detectIframes(renderedHtml), pagination_type: 'click', failure_reason: null
        }
      };
    }
    if (inlineCluster) {
      const text = bodyText.slice(inlineCluster.start, inlineCluster.end);
      return {
        chunks: splitIntoReviewChunks(text),
        diagnostics: {
          review_count_displayed: statedTotal != null ? statedTotal : inlineCluster.count, review_items_collected: inlineCluster.count,
          review_source: 'inline', review_api_url: null, iframe_detected: iframeDetected, pagination_type: 'none', failure_reason: null
        }
      };
    }
    const boardUrl = findReviewBoardLink(renderedHtml, rawUrl) || findReviewBoardLink(html, rawUrl);
    if (boardUrl) {
      const boardResult = await collectFromReviewBoard(boardUrl);
      if (boardResult) return boardResult;
    }
    return {
      chunks: [],
      diagnostics: {
        review_count_displayed: statedTotal, review_items_collected: 0, review_source: 'none', review_api_url: null,
        iframe_detected: detectIframes(renderedHtml), pagination_type: 'none',
        failure_reason: iframeDetected ? 'review iframe detected but content inaccessible' : '리뷰 자체 없음'
      }
    };
  } catch (err) {
    if (inlineCluster) {
      const text = bodyText.slice(inlineCluster.start, inlineCluster.end);
      return {
        chunks: splitIntoReviewChunks(text),
        diagnostics: {
          review_count_displayed: statedTotal != null ? statedTotal : inlineCluster.count, review_items_collected: inlineCluster.count,
          review_source: 'inline', review_api_url: null, iframe_detected: iframeDetected, pagination_type: 'none', failure_reason: null
        }
      };
    }
    return {
      chunks: [],
      diagnostics: {
        review_count_displayed: statedTotal, review_items_collected: 0, review_source: 'none', review_api_url: null,
        iframe_detected: iframeDetected, pagination_type: 'none', failure_reason: 'dynamic rendering failed: ' + err.message
      }
    };
  }
}

// ---------- step 3 fallback: follow a separate review board (Cafe24-style `board_no=4`, etc.) ----------
// Last resort only — a shared board_no can mix in other products' reviews, so this is the least
// trustworthy source and only reached when nothing else (adapter, inline, click-through) worked.
const REVIEW_BOARD_HREF_PATTERNS = [/article\/review/i, /board_no=4/i, /\/board\/review/i, /product_review/i, /\breview\.html/i];
function findReviewBoardLink(html, baseUrl) {
  const hrefs = [...html.matchAll(/href=["']([^"']+)["']/gi)].map((m) => m[1]);
  for (const href of hrefs) {
    if (REVIEW_BOARD_HREF_PATTERNS.some((p) => p.test(href))) {
      try { return new URL(href, baseUrl).toString(); } catch (e) { continue; }
    }
  }
  return null;
}

function withPageParam(urlStr, page) {
  const u = new URL(urlStr);
  u.searchParams.set('page', String(page));
  return u.toString();
}

const MAX_BOARD_PAGES = 5; // bounds pagination so one link can't stall the whole batch
async function collectFromReviewBoard(boardUrl) {
  let combinedText = '';
  let collected = 0;
  let statedTotal = null;
  for (let page = 1; page <= MAX_BOARD_PAGES; page++) {
    let res;
    try {
      res = await fetch(withPageParam(boardUrl, page), {
        redirect: 'follow',
        headers: { 'User-Agent': DEFAULT_UA, 'Accept': 'text/html,application/xhtml+xml' }
      });
    } catch (e) {
      break;
    }
    if (!res.ok) {
      if (page === 1) {
        return {
          chunks: [],
          diagnostics: { review_count_displayed: null, review_items_collected: 0, review_source: 'board', review_api_url: boardUrl, iframe_detected: false, pagination_type: 'page', failure_reason: '리뷰 접근 차단 (' + res.status + ')' }
        };
      }
      break;
    }
    const pageHtml = await res.text();
    if (statedTotal == null) statedTotal = findStatedReviewCount(pageHtml);
    const pageBodyText = stripTags(pageHtml);
    const cluster = findReviewClusterSpan(pageBodyText);
    if (!cluster) break; // no more review-like content — end of the list
    combinedText += pageBodyText.slice(cluster.start, cluster.end) + ' ';
    collected += cluster.count;
    await sleep(400); // stay polite between paginated requests
  }
  if (collected === 0) return null;
  return {
    chunks: splitIntoReviewChunks(combinedText),
    diagnostics: {
      review_count_displayed: statedTotal != null ? statedTotal : collected, review_items_collected: collected,
      review_source: 'board', review_api_url: boardUrl, iframe_detected: false, pagination_type: 'page', failure_reason: null
    }
  };
}

function buildReviewNote(diag) {
  if (diag.failure_reason && diag.review_items_collected === 0) {
    if (/차단/.test(diag.failure_reason)) return '리뷰 접근 차단';
    if (/iframe/i.test(diag.failure_reason)) return '리뷰 영역 발견 / 동적 로딩 실패';
    if (/위젯 감지|widget/i.test(diag.failure_reason)) return '리뷰 영역 발견 / 동적 로딩 실패';
    return '리뷰 자체 없음';
  }
  if (diag.review_items_collected > 0) {
    if (diag.review_source === 'xhr_api') {
      return '리뷰 ' + (diag.review_count_displayed != null ? diag.review_count_displayed : diag.review_items_collected) + '건 확인 / API로 ' + diag.review_items_collected + '건 수집';
    }
    if (diag.review_source === 'board') {
      return '별도 리뷰 게시판 발견 / 본문 ' + diag.review_items_collected + '건 수집';
    }
    const dynLabel = diag.pagination_type === 'click' ? ' (동적 렌더링)' : '';
    return '리뷰 ' + (diag.review_count_displayed != null ? diag.review_count_displayed : diag.review_items_collected) + '건 확인 / 본문 ' + diag.review_items_collected + '건 수집' + dynLabel;
  }
  return '리뷰 자체 없음';
}

// ---------- selling-point analysis: "why buy this" claims, not generic shopping-cart info ----------
// Each concept answers a purchase-decision question directly ("why would I buy this specific
// product") rather than tagging a bare attribute word — synonyms are folded into one canonical
// label by the regex itself ("오래 사용"/"긴 사용기간"/"최대 30일" all -> 장기 지속).
const SELLING_POINT_CONCEPTS = [
  { label: '강력 탈취', category: '성능/효과',
    re: /(냄새|악취)[\s\S]{0,15}(빠르게|바로|즉시|강력히?|확실히?)[\s\S]{0,10}(제거|없애|잡아)|탈취력[\s\S]{0,10}(강력|우수|뛰어남|확실)|(냄새|악취)[\s\S]{0,10}(원인|물질)[\s\S]{0,10}(흡착|분해|제거)/,
    confirmedMarkers: ['강력', '즉시 제거', '바로 제거', '흡착', '분해'] },
  { label: '근본 원인 제거 (마스킹 아님)', category: '성능/효과',
    re: /향으?로?\s?(냄새|악취)를?\s?덮지\s?않고|마스킹(이|하지)?\s?않고|원인[\s\S]{0,10}(부터|물질)[\s\S]{0,10}(제거|분해|흡착)/,
    confirmedMarkers: ['덮지 않고', '원인부터 제거', '원인 물질'] },
  { label: '넓은 공간 커버리지', category: '사용공간',
    re: /\d+\s?평[\s\S]{0,15}(거실|공간|헬스장|사무실|규모)|넓은\s?공간[\s\S]{0,10}(사용|커버|효과|설계)/,
    confirmedMarkers: ['평 규모', '넓은 공간'] },
  { label: '장기 지속', category: '지속력',
    re: /\d+\s?(일|주|개월|시간)[\s\S]{0,10}(사용|지속|유지)|오래\s?지속|긴\s?지속력|지속력[\s\S]{0,6}(우수|좋)/,
    confirmedMarkers: ['지속력', '오래 지속', '오래가'] },
  { label: '재사용 가능', category: '재사용/경제성',
    re: /(전자레인지|건조|세척|햇빛)[\s\S]{0,15}(다시|재사용|반복)[\s\S]{0,10}사용|재사용\s?가능|반복\s?사용|반영구/,
    confirmedMarkers: ['재사용', '반복 사용', '반영구'] },
  { label: '고성능 (수치 비교)', category: '차별기능',
    re: /(기존|일반)\s?(제품)?\s?(대비|보다)[\s\S]{0,10}\d+\s?배|(흡습|흡수)(량|력)[\s\S]{0,10}(높|우수|배|많)/,
    confirmedMarkers: ['배', '대비'] },
  { label: '무향', category: '소재/성분',
    re: /무향|향료?\s?무첨가|향이?\s?없|향료를?\s?넣지\s?않/,
    confirmedMarkers: ['무향', '무첨가'] },
  { label: '공간 활용', category: '사용공간',
    re: /(좁은|작은)\s?(공간|틈|자리)[\s\S]{0,10}(걸어|걸\s?수|보관|활용|사용)|공간\s?활용/,
    confirmedMarkers: ['공간 활용', '좁은 공간'] },
  { label: '교체시점 확인', category: '사용편의',
    re: /색(상)?[\s\S]{0,12}(바뀌|변화|변색)[\s\S]{0,12}(교체|시점|확인)|교체\s?시점/,
    confirmedMarkers: ['교체 시점', '색이 변하면'] },
  { label: '대용량', category: '용량/가성비',
    re: /\d+\s?(g|ml|kg|L|리터)[\s\S]{0,15}(대용량|넉넉|충분|많)|대용량/,
    confirmedMarkers: ['대용량'] },
  { label: '성능 검증', category: '안전/인증',
    re: /(시험|검사|테스트)[\s\S]{0,10}(기관|완료|통과|인증)|공인\s?시험|KOTITI|공인\s?기관|성적서/,
    confirmedMarkers: ['시험 성적서', 'KOTITI', '공인기관'] },
  { label: '간편 사용', category: '사용편의',
    re: /(간편|손쉽게|누구나)[\s\S]{0,10}(사용|설치|교체)/,
    confirmedMarkers: ['간편'] },
  { label: '안전 성분', category: '소재/성분',
    re: /무독성|친환경\s?소재|천연\s?성분|인체\s?무해|안전\s?성분|1등급\s?소재/,
    confirmedMarkers: ['무독성', '친환경', '인체무해'] },
  { label: '독보적 차별화', category: '차별기능',
    re: /유일|독보적|국내\s?최초|비교불가|타의\s?추종/,
    confirmedMarkers: ['유일', '최초', '독보적'] },
  { label: '가벼운 무게', category: '디자인/구조',
    re: /(무게|중량)[\s\S]{0,8}(가볍|경량)|초경량/,
    confirmedMarkers: ['경량', '가벼운'] },
  { label: '컴팩트 디자인', category: '디자인/구조',
    re: /(작고|슬림|콤팩트|컴팩트)[\s\S]{0,10}(디자인|사이즈|크기)/,
    confirmedMarkers: ['컴팩트', '슬림'] },
  { label: '난제거 오염 완벽 제거', category: '성능/효과',
    re: /(안\s?지워지는|잘\s?지워지지\s?않는|지우기\s?힘든|잘\s?빠지지\s?않는)[\s\S]{0,20}(제거|지워|지운다|빠집니다|말끔)|완벽하게\s?(지워|제거)/,
    // both spaced (plain-text pass) and unspaced (OCR pass, after normalizeOcrText joins syllables) forms
    confirmedMarkers: ['안 지워지는', '안지워지는', '지우기 힘든', '지우기힘든', '완벽하게 지워', '완벽하게지워'] },
  { label: '강력한 세정/발포력', category: '성능/효과',
    re: /(고농축|강력한?|파워풀)[\s\S]{0,10}(세정|세척|발포|거품|폼)|high[\s-]?power[\s\S]{0,15}(foam|clean)/i,
    confirmedMarkers: ['고농축', '파워풀', 'high-power', 'High-Power'] }
];

const SELLING_POINT_MIN_SCORE = 2; // below this, treat as noise — never pad the list up to a count
const SELLING_POINT_MAX = 7;

// Extracts text wrapped in heading/emphasis tags from the RAW (untagged-stripped) HTML — a phrase
// the seller bothered to bold or put in a heading is a much stronger "this is the pitch" signal
// than the same phrase buried in a plain paragraph, which a flat bodyText scan can't distinguish.
function extractEmphasizedText(html) {
  const tags = ['h1', 'h2', 'h3', 'strong', 'b', 'em'];
  let combined = '';
  tags.forEach((tag) => {
    const re = new RegExp('<' + tag + '[^>]*>([\\s\\S]*?)<\\/' + tag + '>', 'gi');
    let m;
    while ((m = re.exec(html)) !== null) combined += ' ' + stripTags(m[1]);
  });
  return combined;
}

const SELLING_POINT_TEST_KEYWORDS = ['시험', '인증', 'KOTITI', '검증', '테스트', '공인', '성적서'];
const SELLING_POINT_COMPARATIVE_KEYWORDS = ['대비', '보다', '배', '유일', '최초', '독보적', '비교불가'];

// Shared 4-factor scorer (강조도/반복/근거/차별성), used for both the plain-text pass (bodyText)
// and the OCR fallback pass (text pulled out of detail-page banner images) — kept as one function
// so a fix to the rubric is never applied to only one of the two sources.
function scoreConceptAgainstText(concept, text, opts) {
  const flags = concept.re.flags.includes('g') ? concept.re.flags : concept.re.flags + 'g';
  const globalRe = new RegExp(concept.re.source, flags);
  const matches = [...text.matchAll(globalRe)];
  if (matches.length === 0) return null;

  let emphasisScore;
  let inHero = false;
  if (opts.forcedEmphasisBase != null) {
    // Text pulled out of a designed marketing image IS the emphasis signal itself — there's no
    // separate heading/bold tag to check because OCR output carries no HTML structure.
    emphasisScore = Math.min(3, opts.forcedEmphasisBase);
  } else {
    const inEmphasis = opts.emphasized != null && concept.re.test(opts.emphasized);
    inHero = opts.heroLen != null && matches.some((m) => m.index < opts.heroLen);
    emphasisScore = Math.min(3, (inEmphasis ? 2 : 0) + (inHero ? 1 : 0));
  }

  // 반복 언급 0-2 — a single clear statement still counts (1점); repeated emphasis adds the 2nd point.
  // A one-off honest claim shouldn't be zeroed out just because the seller only said it once.
  const repetitionScore = matches.length >= 4 ? 2 : matches.length >= 1 ? 1 : 0;

  // 근거(숫자/시험) 0-3, using a window around the first match as the evidence quote
  const first = matches[0];
  const windowStart = Math.max(0, first.index - 30);
  const windowEnd = Math.min(text.length, first.index + first[0].length + 60);
  const evidenceWindow = text.slice(windowStart, windowEnd).trim();
  const evidenceScore = Math.min(3, (/\d/.test(evidenceWindow) ? 1 : 0) + (SELLING_POINT_TEST_KEYWORDS.some((k) => evidenceWindow.includes(k)) ? 2 : 0));

  // 차별성 0-2
  const diffScore = SELLING_POINT_COMPARATIVE_KEYWORDS.some((k) => evidenceWindow.includes(k)) ? 2 : 0;

  const score = emphasisScore + repetitionScore + evidenceScore + diffScore;
  // "확정 소구": the canonical phrase itself (or a close marker) is literally on the page.
  // "추론 소구": we combined a bare attribute + modifier into this label without that exact wording.
  const confirmed = concept.confirmedMarkers.some((marker) => text.includes(marker));

  return {
    point: concept.label,
    category: concept.category,
    evidence: evidenceWindow,
    source: opts.singleSource || (inHero ? opts.sourceHero : opts.sourceBody),
    score,
    confirmed: confirmed ? 'confirmed' : 'inferred',
    count: score // kept for the aggregation code elsewhere that already sums sp.count across products
  };
}

// ocrText is optional — text OCR'd from detail-page banner images (see collectDetailImageUrls /
// ocrImages below), used as a fallback source when a page bakes its whole pitch into image design
// instead of real HTML text. When both the plain-text and OCR passes find the same concept, the
// higher-scoring one wins — we never double-count a claim as two separate points.
function scoreSellingPoints(html, bodyText, ocrText) {
  const emphasized = extractEmphasizedText(html);
  const heroLen = Math.floor(bodyText.length * 0.15);

  const results = [];
  SELLING_POINT_CONCEPTS.forEach((concept) => {
    const fromText = scoreConceptAgainstText(concept, bodyText, {
      emphasized, heroLen,
      sourceHero: '상세페이지 상단(강조 영역)',
      sourceBody: '상세페이지 본문'
    });
    const fromOcr = ocrText ? scoreConceptAgainstText(concept, ocrText, {
      forcedEmphasisBase: 2,
      singleSource: '상세페이지 이미지(OCR)'
    }) : null;

    const best = [fromText, fromOcr].filter(Boolean).sort((a, b) => b.score - a.score)[0];
    if (best) results.push(best);
  });

  return results.sort((a, b) => b.score - a.score).filter((r) => r.score >= SELLING_POINT_MIN_SCORE).slice(0, SELLING_POINT_MAX);
}

// ---------- OCR fallback for image-based detail pages ----------
// Some sellers bake their entire pitch into designed banner images inside the description area —
// there is no HTML text there at all for scoreSellingPoints' plain-text pass to read (confirmed by
// inspection: codenit.co.kr's detail area is ~1KB of checkout UI text plus 10+ full-size banner
// images). This renders the page with Playwright, finds banner-sized images (real photos/graphics,
// not tiny UI icons — filtered by rendered pixel size), OCRs each with Tesseract (kor+eng), and
// feeds the extracted text through the same scoreConceptAgainstText scorer as plain body text.
const MAX_OCR_IMAGES = 4; // OCR is slow (multi-second per image) — bounds worst-case latency per product
const OCR_MIN_WIDTH = 300;
const OCR_MIN_HEIGHT = 200;

let ocrWorkerPromise = null;
function getOcrWorker() {
  if (!ocrWorkerPromise) ocrWorkerPromise = createWorker(['eng', 'kor']);
  return ocrWorkerPromise;
}
// Tesseract workers process one recognize() call at a time — serialize like the Playwright queue.
let ocrQueue = Promise.resolve();
function runOcrExclusive(fn) {
  const run = ocrQueue.then(fn, fn);
  ocrQueue = run.then(() => {}, () => {});
  return run;
}

// Tesseract frequently over-segments Hangul into one-syllable tokens ("지 워 지 는" instead of
// "지워지는"), which silently breaks every concept regex expecting normal word spacing. Collapse
// runs of 3+ single-character tokens back into words before matching; leaves real multi-character
// words (which never look like "X <space> X <space> X") untouched.
function normalizeOcrText(text) {
  return text.replace(/(?:\S\s){2,}\S/g, (run) => run.replace(/\s+/g, ''));
}

async function collectDetailImageUrls(rawUrl) {
  return runExclusive(async () => {
    const browser = await getBrowser();
    const context = await browser.newContext({ userAgent: DEFAULT_UA, locale: 'ko-KR' });
    const page = await context.newPage();
    try {
      await page.goto(rawUrl, { waitUntil: 'domcontentloaded', timeout: FETCH_TIMEOUT_MS });
      for (const label of ['상세정보', '상세 정보', 'PRODUCT INFO', 'Detail']) {
        try {
          const locator = page.getByText(label, { exact: false }).first();
          if (await locator.count() > 0) { await locator.click({ timeout: 1500 }); break; }
        } catch (e) { /* tab not present/clickable — description content may already be visible */ }
      }
      // Nudge lazy-loaded (IntersectionObserver-based) images into loading by scrolling through.
      for (let i = 0; i < 6; i++) {
        await page.evaluate((step) => window.scrollBy(0, step), 1200);
        await page.waitForTimeout(250);
      }
      await page.waitForTimeout(500);

      const urls = await page.evaluate(({ minW, minH }) => {
        return Array.from(document.querySelectorAll('img'))
          .filter((img) => img.naturalWidth >= minW && img.naturalHeight >= minH)
          .map((img) => img.currentSrc || img.src)
          .filter(Boolean);
      }, { minW: OCR_MIN_WIDTH, minH: OCR_MIN_HEIGHT });

      return [...new Set(urls)];
    } finally {
      await context.close();
    }
  });
}

async function ocrImages(urls) {
  if (!urls.length) return { text: '', diagnostics: { considered: 0, ocred: 0, extractedChars: 0 } };
  const picked = urls.slice(0, MAX_OCR_IMAGES);
  const worker = await getOcrWorker();
  const texts = [];
  let ocred = 0;
  for (const url of picked) {
    try {
      const imgRes = await fetch(url);
      if (!imgRes.ok) { console.log('[ocr] image fetch failed', url, imgRes.status); continue; }
      const buf = Buffer.from(await imgRes.arrayBuffer());
      const result = await runOcrExclusive(() => worker.recognize(buf));
      ocred++;
      const t = normalizeOcrText((result.data.text || '').replace(/\s+/g, ' ').trim());
      if (t) texts.push(t);
    } catch (e) {
      console.log('[ocr] recognize failed on', url, '-', e.message);
    }
  }
  const combined = texts.join(' ');
  return { text: combined, diagnostics: { considered: urls.length, ocred, extractedChars: combined.length } };
}

// chunks: array of already-isolated review texts (one per real review when the source is a
// structured API; date-cluster-split segments otherwise). Never the whole page body.
// ---------- fully-instrumented keyword pipeline ----------
// Traces every stage to the console by name (raw_reviews -> ... -> final_negative_keywords) so a
// "collected N reviews but 0 keywords" report can be diagnosed from logs alone: is it the reviews
// that are empty, the regex matching, the frequency filter, or a field-name mismatch upstream?
// Single shared classifier used BOTH for the whole-review positive/negative/neutral breakdown AND
// for attribute-level candidate extraction — using two different code paths for those two things
// is exactly how a "review IS negative but 0 candidates extracted" bug hides: they'd disagree with
// no way to tell which one is wrong. Sharing one function makes that class of bug impossible.
function classifyReview(text) {
  const positiveLabels = [];
  const negativeLabels = [];
  POSITIVE_CONCEPTS.forEach((c) => { if (c.re.test(text)) positiveLabels.push(c.label); });
  NEGATIVE_CONCEPTS.forEach((c) => { if (c.re.test(text)) negativeLabels.push(c.label); });
  // generic fallback only when NO specific attribute fired for that polarity — "가격이 비싸서
  // 아쉬워요" already got '가격 부담' above, so the generic 아쉬움 check below is skipped for it.
  if (positiveLabels.length === 0 && GENERIC_POSITIVE_WORDS.some((w) => text.includes(w))) {
    positiveLabels.push('전반적 만족');
  }
  if (negativeLabels.length === 0) {
    if (GENERIC_NEGATIVE_DISSATISFIED_WORDS.some((w) => text.includes(w))) negativeLabels.push('전반적 불만');
    else if (GENERIC_NEGATIVE_REGRET_WORDS.some((w) => text.includes(w))) negativeLabels.push('전반적 아쉬움');
  }
  return { positiveLabels, negativeLabels };
}

function runKeywordPipeline(rawReviews) {
  console.log('[keywordAnalyzer] input count:', rawReviews.length);
  console.log('[keywordAnalyzer] input sample:', JSON.stringify(rawReviews.slice(0, 3).map((r) => String(r).slice(0, 100))));

  // [1] raw_reviews
  console.log('[1] raw_reviews: input=' + rawReviews.length + ' output=' + rawReviews.length);
  rawReviews.slice(0, 5).forEach((r, i) => console.log('  raw[' + i + ']: ' + String(r).slice(0, 140)));

  // [2] normalized_reviews — collapse whitespace, drop anything empty after that
  const normalized = rawReviews.map((r) => String(r || '').replace(/\s+/g, ' ').trim()).filter((r) => r.length > 0);
  console.log('[2] normalized_reviews: input=' + rawReviews.length + ' output=' + normalized.length +
    (rawReviews.length !== normalized.length ? ' removed=' + (rawReviews.length - normalized.length) + ' (empty after normalize)' : ''));
  normalized.slice(0, 5).forEach((r, i) => console.log('  norm[' + i + ']: ' + r.slice(0, 140)));

  // ---- whole-review classification pass (positive_reviews / negative_reviews / neutral_reviews) ----
  // Runs BEFORE keyword extraction and reuses the exact same classifyReview() the candidates below
  // use, so this count can never diverge from what stage [3] finds per review.
  const classifications = normalized.map((text) => classifyReview(text));
  const positiveReviewCount = classifications.filter((c) => c.positiveLabels.length > 0).length;
  const negativeReviewCount = classifications.filter((c) => c.negativeLabels.length > 0).length;
  const neutralReviewCount = classifications.filter((c) => c.positiveLabels.length === 0 && c.negativeLabels.length === 0).length;
  console.log('positive_reviews: ' + positiveReviewCount);
  console.log('negative_reviews: ' + negativeReviewCount);
  console.log('neutral_reviews: ' + neutralReviewCount);
  if (negativeReviewCount > 0) {
    console.log('[NEGATIVE REVIEWS — full text]');
    normalized.forEach((text, idx) => {
      if (classifications[idx].negativeLabels.length > 0) {
        console.log('[NEGATIVE REVIEW] "' + text + '" → ' + classifications[idx].negativeLabels.join(', '));
      }
    });
  } else {
    console.log('[negative-pipeline] negative_reviews = 0 — no review matched any negative concept or generic negative word');
  }

  // [3] extracted_candidates — same classification result, flattened to one candidate per label hit.
  const candidates = [];
  normalized.forEach((text, idx) => {
    classifications[idx].positiveLabels.forEach((label) => candidates.push({ reviewIndex: idx, label, polarity: 'positive', snippet: text.slice(0, 90) }));
    classifications[idx].negativeLabels.forEach((label) => candidates.push({ reviewIndex: idx, label, polarity: 'negative', snippet: text.slice(0, 90) }));
  });
  const negCandidatesBeforeFilter = candidates.filter((c) => c.polarity === 'negative');
  console.log('[3] extracted_candidates: input=' + normalized.length + ' output=' + candidates.length +
    (candidates.length === 0 ? ' (no attribute or generic-sentiment match in any review)' : ''));
  candidates.slice(0, 8).forEach((c) => console.log('  "' + c.snippet + '" → ' + c.label + ' / ' + c.polarity));
  console.log('negative_candidates_before_filter: ' + negCandidatesBeforeFilter.length);
  negCandidatesBeforeFilter.slice(0, 8).forEach((c) => console.log('  - ' + c.snippet + ' → ' + c.label));

  // [4] sentiment_classified — polarity is assigned during extraction; this stage confirms nothing
  // was left unclassified before merging.
  const unclassified = candidates.filter((c) => c.polarity !== 'positive' && c.polarity !== 'negative');
  console.log('[4] sentiment_classified: input=' + candidates.length + ' output=' + (candidates.length - unclassified.length) +
    (unclassified.length ? ' removed=' + unclassified.length + ' (no polarity assigned)' : ''));
  console.log('negative_candidates_after_normalization: ' + negCandidatesBeforeFilter.length + ' (normalization happens before extraction — count unchanged here)');

  // [5] merged_keywords — group by canonical label, counting DISTINCT reviews (not raw mentions),
  // so the same phrase repeated within one review only counts once.
  const merged = {};
  candidates.forEach((c) => {
    if (!merged[c.label]) merged[c.label] = { polarity: c.polarity, reviewIndexes: new Set() };
    merged[c.label].reviewIndexes.add(c.reviewIndex);
  });
  let mergedList = Object.keys(merged).map((label) => ({ label, polarity: merged[label].polarity, count: merged[label].reviewIndexes.size }));
  console.log('[5] merged_keywords: input=' + candidates.length + ' output=' + mergedList.length);
  mergedList.forEach((m) => console.log('  ' + m.label + ' (' + m.polarity + '): ' + m.count + '건'));
  const negMergedList = mergedList.filter((m) => m.polarity === 'negative');
  console.log('negative_candidates_after_merge: ' + negMergedList.length);
  negMergedList.forEach((m) => console.log('  ' + m.label + ': ' + m.count + '건'));

  // [6] frequency_filtered — SAME adaptive threshold for both polarities (this is exactly what the
  // "is there a stricter rule hiding on the negative side?" question needed verifying: there isn't —
  // filtered/droppedByFreq below apply identically regardless of m.polarity).
  const minFreq = minFrequencyFor(normalized.length);
  const filtered = mergedList.filter((m) => m.count >= minFreq);
  const droppedByFreq = mergedList.filter((m) => m.count < minFreq);
  console.log('[6] frequency_filtered: input=' + mergedList.length + ' output=' + filtered.length +
    ' min_frequency=' + minFreq + ' (based on ' + normalized.length + ' reviews, same rule for both polarities)');
  droppedByFreq.forEach((m) => console.log('  removed: ' + m.label + ' (' + m.polarity + ', count=' + m.count + ' < ' + minFreq + ')'));
  const negFiltered = filtered.filter((m) => m.polarity === 'negative');
  console.log('negative_candidates_after_frequency_filter: ' + negFiltered.length);

  // [7]/[8] final positive/negative — NOT padded to 5; only what actually survived
  let positive = filtered.filter((m) => m.polarity === 'positive').sort((a, b) => b.count - a.count).slice(0, 5);
  let negative = filtered.filter((m) => m.polarity === 'negative').sort((a, b) => b.count - a.count).slice(0, 5);
  console.log('[7] final_positive_keywords: ' + JSON.stringify(positive));
  console.log('[8] final_negative_keywords: ' + JSON.stringify(negative));

  // Distinguish "genuinely no negative opinions" from "found some but the pipeline lost them" —
  // classifyReview() being shared between the review-level pass and candidate extraction means the
  // second case should be structurally impossible (adaptive min_frequency=1 keeps every single
  // mention below 30 reviews), but we verify explicitly rather than assume our own reasoning holds.
  if (negativeReviewCount === 0) {
    console.log('[negative-pipeline] 부정 의견 없음 (정상 — ' + normalized.length + '건 중 부정으로 분류된 리뷰 없음)');
  } else if (negative.length === 0) {
    console.log('[negative-pipeline] 부정 리뷰 분석 실패 — negative_reviews=' + negativeReviewCount + '건 발견됐으나 최종 부정 키워드 0건. 파이프라인 점검 필요.');
  } else {
    console.log('[negative-pipeline] 정상 — negative_reviews=' + negativeReviewCount + '건 중 ' + negative.length + '개 키워드로 통합됨');
  }

  // Fallback: reviews existed in real volume but NOTHING survived on EITHER side — re-run the
  // generic-sentiment pass alone at min_frequency=1. (With classifyReview shared above this should
  // rarely trigger anymore; kept as a last-resort safety net, not as the primary mechanism.)
  if (normalized.length >= 3 && positive.length === 0 && negative.length === 0) {
    console.log('[fallback] reviews>=3 but 0 keywords survived filtering on either side — re-running generic sentiment pass at min_frequency=1');
    const fb = {};
    normalized.forEach((text, idx) => {
      if (GENERIC_POSITIVE_WORDS.some((w) => text.includes(w))) {
        fb['전반적 만족'] = fb['전반적 만족'] || { polarity: 'positive', reviewIndexes: new Set() };
        fb['전반적 만족'].reviewIndexes.add(idx);
      }
      if (GENERIC_NEGATIVE_DISSATISFIED_WORDS.some((w) => text.includes(w))) {
        fb['전반적 불만'] = fb['전반적 불만'] || { polarity: 'negative', reviewIndexes: new Set() };
        fb['전반적 불만'].reviewIndexes.add(idx);
      } else if (GENERIC_NEGATIVE_REGRET_WORDS.some((w) => text.includes(w))) {
        fb['전반적 아쉬움'] = fb['전반적 아쉬움'] || { polarity: 'negative', reviewIndexes: new Set() };
        fb['전반적 아쉬움'].reviewIndexes.add(idx);
      }
    });
    const fbList = Object.keys(fb).map((label) => ({ label, polarity: fb[label].polarity, count: fb[label].reviewIndexes.size }));
    positive = fbList.filter((m) => m.polarity === 'positive').sort((a, b) => b.count - a.count).slice(0, 5);
    negative = fbList.filter((m) => m.polarity === 'negative').sort((a, b) => b.count - a.count).slice(0, 5);
    console.log('[fallback] result positive=' + JSON.stringify(positive) + ' negative=' + JSON.stringify(negative));
  }

  return {
    positive: positive.map((m) => ({ keyword: m.label, count: m.count })),
    negative: negative.map((m) => ({ keyword: m.label, count: m.count }))
  };
}

function extractReviewKeywordsFromChunks(chunks) {
  return runKeywordPipeline(chunks);
}

async function analyzeProductPage(rawUrl, html) {
  const meta = extractBasicMeta(html);
  const bodyText = stripTags(html);
  const price = extractPrice(html, bodyText);
  const weight = extractWeight(bodyText, meta.title);
  const unitPrice = computeUnitPrice(price, weight);
  let sellingPoints = scoreSellingPoints(html, bodyText);
  console.log('[selling-points]', rawUrl, 'text pass (concept dictionary) found', sellingPoints.length, '(min_score=' + SELLING_POINT_MIN_SCORE + ', cap=' + SELLING_POINT_MAX + ')');

  // A thin result here can mean the real pitch is baked into detail-page banner images (confirmed
  // case: codenit.co.kr) rather than "this product genuinely has no selling points" — OCR the
  // images and re-run the SAME concept dictionary against that text before accepting an empty
  // result. Deliberately does NOT fall back further to raw/uninterpreted text: a literal sentence
  // fragment (especially noisy OCR output) is evidence, not a selling point, and showing it as one
  // reads as nonsensical to someone doing real product planning — better to honestly report nothing
  // found than to guess.
  // Gated behind ENABLE_OCR (default off): loading Tesseract's WASM engine + kor+eng language
  // models sits in memory for the process's whole lifetime, and on a 512MB host that's enough on
  // its own to push Chromium + Node over the limit and get OOM-killed. Off by default so the
  // deployed app runs lean; set ENABLE_OCR=true locally (more headroom) to get the OCR fallback.
  if (sellingPoints.length < 3 && process.env.ENABLE_OCR === 'true') {
    try {
      const imageUrls = await collectDetailImageUrls(rawUrl);
      console.log('[selling-points][ocr]', rawUrl, 'detail images considered=' + imageUrls.length, '(min ' + OCR_MIN_WIDTH + 'x' + OCR_MIN_HEIGHT + 'px)');
      if (imageUrls.length) {
        const ocrResult = await ocrImages(imageUrls);
        console.log('[selling-points][ocr]', rawUrl, 'images_ocred=' + ocrResult.diagnostics.ocred, 'extracted_chars=' + ocrResult.diagnostics.extractedChars);
        if (ocrResult.text) {
          console.log('[selling-points][ocr] sample text:', ocrResult.text.slice(0, 300));
          sellingPoints = scoreSellingPoints(html, bodyText, ocrResult.text);
          console.log('[selling-points][ocr]', rawUrl, 'after OCR + concept dictionary found', sellingPoints.length, '(min_score=' + SELLING_POINT_MIN_SCORE + ', cap=' + SELLING_POINT_MAX + ')');
        }
      }
    } catch (e) {
      console.log('[selling-points][ocr] fallback failed:', e.message);
    }
  }
  sellingPoints.forEach((sp) => console.log(`  "${sp.evidence}" → ${sp.point} [${sp.category}/${sp.confirmed}] score=${sp.score} source=${sp.source}`));

  const review = await collectReviewData(rawUrl, html);
  const keywords = extractReviewKeywordsFromChunks(review.chunks);
  const reviewNote = buildReviewNote(review.diagnostics);

  const d = review.diagnostics;
  console.log(
    '[review]', rawUrl,
    'review_count_displayed=' + d.review_count_displayed,
    'review_items_collected=' + d.review_items_collected,
    'review_source=' + d.review_source,
    'review_api_url=' + d.review_api_url,
    'iframe_detected=' + d.iframe_detected,
    'pagination_type=' + d.pagination_type,
    'failure_reason=' + d.failure_reason
  );
  if (review.chunks.length > 0) {
    console.log('[review] sample collected reviews (up to 5):');
    review.chunks.slice(0, 5).forEach((c, i) => console.log(`  [${i + 1}] ${c.slice(0, 200)}`));
  }
  if (Array.isArray(review.ratings) && review.ratings.some((r) => r != null)) {
    const low = review.ratings.filter((r) => r != null && r <= 2).length;
    const mid = review.ratings.filter((r) => r === 3).length;
    const high = review.ratings.filter((r) => r != null && r >= 4).length;
    console.log(`[review] star ratings (auxiliary signal only, not used to invent keywords): 1-2★=${low} 3★=${mid} 4-5★=${high}`);
  }

  return {
    title: meta.title,
    image: meta.image,
    price,
    weight,
    unitPrice,
    positiveKeywords: keywords.positive,
    negativeKeywords: keywords.negative,
    sellingPoints,
    reviewNote
  };
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function fetchOne(rawUrl, attempt = 1) {
  let url;
  try {
    url = new URL(rawUrl);
  } catch (e) {
    return { url: rawUrl, ok: false, error: '올바른 URL 형식이 아닙니다.' };
  }
  if (url.protocol !== 'http:' && url.protocol !== 'https:') {
    return { url: rawUrl, ok: false, error: '지원하지 않는 URL 형식입니다.' };
  }

  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), FETCH_TIMEOUT_MS);
  try {
    const res = await fetch(url.toString(), {
      redirect: 'follow',
      signal: controller.signal,
      headers: {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8'
      }
    });
    // 429 = rate limited, not blocked — wait once (respecting Retry-After if given) and retry a single time
    if (res.status === 429 && attempt === 1) {
      clearTimeout(timer);
      const retryAfter = Number(res.headers.get('retry-after'));
      const waitMs = Number.isFinite(retryAfter) && retryAfter > 0 ? Math.min(retryAfter * 1000, 8000) : 2000;
      await sleep(waitMs);
      return fetchOne(rawUrl, 2);
    }
    if (!res.ok) {
      return { url: rawUrl, ok: false, status: res.status, error: `사이트에서 ${res.status} 응답 — 접근이 제한된 페이지일 수 있어요.` };
    }
    const contentType = res.headers.get('content-type') || '';
    if (!/text\/html|application\/xhtml/.test(contentType)) {
      return { url: rawUrl, ok: false, error: '페이지 내용을 읽을 수 없는 형식입니다 (' + (contentType || '알 수 없음') + ')' };
    }
    const html = await res.text();
    const analysis = await analyzeProductPage(rawUrl, html);
    if (!analysis.title && analysis.price == null) {
      return { url: rawUrl, ok: false, error: '페이지에서 정보를 찾지 못했어요 (자바스크립트 렌더링 페이지이거나 접근 제한일 수 있어요).' };
    }
    return {
      url: rawUrl,
      ok: true,
      finalUrl: res.url,
      title: analysis.title,
      image: analysis.image,
      price: analysis.price,
      weight: analysis.weight,
      unitPrice: analysis.unitPrice,
      positiveKeywords: analysis.positiveKeywords,
      negativeKeywords: analysis.negativeKeywords,
      sellingPoints: analysis.sellingPoints,
      purchaseConditions: analysis.purchaseConditions,
      reviewNote: analysis.reviewNote
    };
  } catch (err) {
    const msg = err.name === 'AbortError' ? '응답 시간 초과 (사이트가 응답하지 않음)' : (err.message || '알 수 없는 오류');
    return { url: rawUrl, ok: false, error: msg };
  } finally {
    clearTimeout(timer);
  }
}

const server = http.createServer((req, res) => {
  if (req.method === 'POST' && req.url === '/api/fetch-links') {
    let body = '';
    let tooLarge = false;
    req.on('data', (chunk) => {
      body += chunk;
      if (body.length > MAX_BODY_BYTES) { tooLarge = true; req.destroy(); }
    });
    req.on('end', async () => {
      if (tooLarge) return;
      let payload;
      try {
        payload = JSON.parse(body || '{}');
      } catch (e) {
        return sendJson(res, 400, { error: '잘못된 요청 형식입니다.' });
      }
      let links = Array.isArray(payload.links) ? payload.links : [];
      links = links.map((s) => String(s || '').trim()).filter(Boolean).slice(0, MAX_LINKS);
      if (links.length === 0) return sendJson(res, 400, { error: '링크를 1개 이상 입력해주세요.' });
      // stagger request start times so we don't hit the same host with a burst all at once
      // (a common trigger for simple rate-limit 429s, independent of any per-site block)
      const STAGGER_MS = 350;
      const results = await Promise.all(
        links.map((link, i) => sleep(i * STAGGER_MS).then(() => fetchOne(link)))
      );
      sendJson(res, 200, { results, sellingPointLexicon: SELLING_POINT_CONCEPTS.map((c) => c.label) });
    });
    return;
  }

  if (req.method !== 'GET') {
    res.writeHead(405);
    return res.end('Method Not Allowed');
  }

  let reqPath = decodeURIComponent(req.url.split('?')[0]);
  if (reqPath === '/') reqPath = '/index.html';
  const filePath = path.normalize(path.join(publicPath, reqPath));
  if (!filePath.startsWith(publicPath)) {
    res.writeHead(403);
    return res.end('Forbidden');
  }
  fs.readFile(filePath, (err, data) => {
    if (err) {
      res.writeHead(404);
      return res.end('Not found');
    }
    const ext = path.extname(filePath);
    res.writeHead(200, { 'Content-Type': MIME[ext] || 'application/octet-stream', 'Cache-Control': 'no-store' });
    res.end(data);
  });
});

server.listen(port, () => {
  console.log(`신제품 기획 보드 서버 실행 중: http://localhost:${port}`);
});
