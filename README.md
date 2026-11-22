# 말로 캐드 (VoiceCAD)

말(음성·글)과 손으로 쓰는 브라우저 캐드. 2D 도면을 바탕으로 3D를 구성·모델링하는 것이 목표다 (3D 단계 계획: [docs/3D_계획.md](docs/3D_계획.md)).

- `index.html` — 캐드 본체(화면·기본 명령·AI·서버 저장). 브라우저에서 바로 동작.
- `cad-cmds.js` — 실제 캐드 명령 확장. 사람이 쓰는 명령과 AI(`apply_drawing`의 `ops`)가 같은 기하 함수를 쓴다.
  그리기·수정·치수·레이어·스냅·그립·블록·해치, DWG/DXF 열기, DWG 저장, 외부 참조, 출력(PDF·인쇄), 3D 보기.
- `cad-3d.js` — 3D 모델링. 도면 화면을 3D로 바꿔 보기(돌려보기·방향·보기 방식), 입체(`type:'solid'`) 명령(상자·원기둥·원뿔·구·밀어올리기·누르고 당기기), OBJ·STL 내보내기, AI용 입체·`EXTRUDE`/`VIEW3D`/`PLAN` ops.
- `vendor/acad-ts-3.6.0.min.js` — DWG 읽기·쓰기 라이브러리(아래 오픈소스 고지). DWG를 열거나 저장할 때만 불러온다.
- `gen3d.py` — 3D 생성기. `elements_*.json`(캐드의 「3D용 내보내기」)을 읽어 Blender로 모델·렌더 생성.
  `blender --background --python gen3d.py -- <elements.json 절대경로> <출력접두어 절대경로>`

배포: GitHub Pages. 인허가 브릿지(`/permit-bridge/`)와 같은 도메인이라 「이 대지에 도면 그리기」 버튼이 `localStorage['pb.handoff']`로 대지·법규 데이터를 넘긴다.
도면 저장과 AI 호출은 회사 서버 API를 거친다(사내 계정 로그인 필요). Claude API 키는 서버에만 있고 저장소·브라우저에는 없다.
DWG·DXF·PDF 파일은 브라우저 안에서만 읽고 변환하며 서버로 보내지 않는다.

## 오픈소스 고지

| 소프트웨어 | 쓰는 곳 | 저작권 | 라이선스 |
|---|---|---|---|
| [acad-ts](https://github.com/node-projects/acad-ts) 3.6.0 | DWG 열기·저장 (`vendor/`, 원본 그대로) | Copyright (c) 2026 Jochen Kühner, Copyright (c) 2021 Albert Domenech | MIT (`vendor/acad-ts-LICENSE.txt`) |
| [three.js](https://github.com/mrdoob/three.js) r170 | 3D 화면 (처음 3D를 열 때 jsDelivr에서 받음) | Copyright © 2010-2024 three.js authors | MIT |
| [PDF.js](https://github.com/mozilla/pdf.js) 3.11.174 | PDF → CAD 변환 (쓸 때 cdnjs에서 받음) | Mozilla Foundation | Apache License 2.0 |

AutoCAD, DWG는 Autodesk, Inc.의 상표입니다. 말로 캐드는 Autodesk와 관계없는 독립 프로그램입니다.
