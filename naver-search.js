import process from 'node:process';

const clientId = process.env.NAVER_CLIENT_ID;
const clientSecret = process.env.NAVER_CLIENT_SECRET;

if (!clientId || !clientSecret) {
  console.error('NAVER_CLIENT_ID / NAVER_CLIENT_SECRET이 설정되지 않았습니다. .env 파일을 확인하세요 (.env.example 참고).');
  process.exit(1);
}

const keyword = process.argv.slice(2).join(' ') || '차량용 방향제';

const url = new URL('https://openapi.naver.com/v1/search/shop.json');
url.searchParams.set('query', keyword);
url.searchParams.set('display', '10');
// 네이버 쇼핑 API는 판매량순 정렬을 제공하지 않는다 (sim=정확도순, date=날짜순, asc/dsc=가격순)
url.searchParams.set('sort', 'sim');

function stripTags(s) {
  return s.replace(/<[^>]*>/g, '');
}

function fmtWon(n) {
  return Number(n).toLocaleString('ko-KR') + '원';
}

const res = await fetch(url, {
  headers: {
    'X-Naver-Client-Id': clientId,
    'X-Naver-Client-Secret': clientSecret
  }
});

if (!res.ok) {
  const body = await res.text();
  console.error(`네이버 API 호출 실패: ${res.status} ${res.statusText}`);
  console.error(body);
  process.exit(1);
}

const data = await res.json();

console.log(`\n"${keyword}" 검색 결과 (총 ${Number(data.total).toLocaleString('ko-KR')}건 중 상위 ${data.items.length}건, 정확도순)\n`);

data.items.forEach((item, i) => {
  console.log(`${i + 1}. ${stripTags(item.title)}`);
  console.log(`   가격: ${fmtWon(item.lprice)}  |  판매처: ${item.mallName}`);
  console.log(`   링크: ${item.link}`);
  console.log('');
});
