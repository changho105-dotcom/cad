# 말로 캐드 (VoiceCAD)

말(음성·글)로 건축 2D 도면을 그리고, 그 2D 요소 데이터에서 입면·단면·3D를 계산해 만드는 건축 특화 캐드.

- `index.html` — 캐드 본체 (단일 파일, 외부 라이브러리 없음). 브라우저에서 바로 동작.
- `gen3d.py` — 3D 생성기. `elements_*.json`(캐드의 「3D용 내보내기」)을 읽어 Blender로 모델·렌더 생성.
  `blender --background --python gen3d.py -- <elements.json 절대경로> <출력접두어 절대경로>`

배포: GitHub Pages. 인허가 브릿지(`/permit-bridge/`)와 같은 도메인이라 「이 대지에 도면 그리기」 버튼이 `localStorage['pb.handoff']`로 대지·법규 데이터를 넘긴다.
도면 저장과 AI 호출은 회사 서버 API를 거친다(사내 계정 로그인 필요). Claude API 키는 서버에만 있고 저장소·브라우저에는 없다.
