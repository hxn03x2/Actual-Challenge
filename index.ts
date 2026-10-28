import { createClient } from "npm:@supabase/supabase-js@2";

const corsHeaders = {
  "Access-Control-Allow-Origin": "*",
  "Access-Control-Allow-Headers": "authorization, apikey, content-type",
  "Access-Control-Allow-Methods": "POST, OPTIONS",
};
const json = (body: unknown, status = 200) => new Response(JSON.stringify(body), {
  status, headers: { ...corsHeaders, "Content-Type": "application/json" },
});
const enc = new TextEncoder();
const b64url = (bytes: Uint8Array) => btoa(String.fromCharCode(...bytes)).replace(/=/g, "").replace(/\+/g, "-").replace(/\//g, "_");
const fromB64url = (s: string) => Uint8Array.from(atob(s.replace(/-/g, "+").replace(/_/g, "/") + "=".repeat((4 - s.length % 4) % 4)), c => c.charCodeAt(0));
const encodeJson = (v: unknown) => b64url(enc.encode(JSON.stringify(v)));
const normalizeSubject = (v: unknown) => String(v ?? "").replace(/\s+/g, "").toLowerCase();
const subjectArea = (v: unknown) => {
  const s = String(v ?? "");
  return s.split(/\s*[\/·]\s*/).pop()?.trim() ?? s.trim();
};
const isEnglish = (v: unknown) => ["영어영역", "english"].includes(normalizeSubject(subjectArea(v)));
const isInquiry = (v: unknown) => ["사회탐구영역", "과학탐구영역"].includes(normalizeSubject(subjectArea(v)));
const absoluteGrade = (score: number, english: boolean) => {
  const cuts = english ? [90,80,70,60,50,40,30,20] : [40,35,30,25,20,15,10,5];
  const found = cuts.findIndex(c => score >= c);
  return found < 0 ? 9 : found + 1;
};
const validScore = (v: number, max: number) => Number.isFinite(v) && v >= 0 && v <= max && Math.abs(v * 10 - Math.round(v * 10)) < 1e-6;
const maxScoreForSubject = (subject: unknown) => isInquiry(subject) ? 50 : 100;

// ---------------------------------------------------------------------------
// 시험 정보 (학년도, 학년, 시험 종류, 응시 일자, 영역) 처리
// ---------------------------------------------------------------------------
const BUCKET = "mock-exam-files";
const TYPE_CODES: Record<string, string> = {"3월 전국연합학력평가":"3n","5월 전국연합학력평가":"5n","6월 대학수학능력시험 모의평가":"6m","6월 전국연합학력평가":"6n","7월 전국연합학력평가":"7n","9월 대학수학능력시험 모의평가":"9m","9월 전국연합학력평가":"9n","10월 전국연합학력평가":"10n","11월 대학수학능력시험":"11s"};
const TYPE_LABELS: Record<string, string> = Object.fromEntries(Object.entries(TYPE_CODES).map(([k, v]) => [v, k]));
const LOWER_GRADE_CODES = ["3n", "6n", "9n", "10n"];
const AREA_LABELS: Record<string, string> = { korean: "국어 영역", math: "수학 영역", english: "영어 영역", social: "사회탐구 영역", science: "과학탐구 영역" };
const AREA_CODES: Record<string, string> = Object.fromEntries(Object.entries(AREA_LABELS).map(([k, v]) => [v, k]));
const AREA_LABELS_LEGACY: Record<string, string> = { ...AREA_LABELS, inquiry: "탐구", "all-subjects": "전체 과목" };
const CATEGORY_LABELS: Record<string, string> = { paper: "문제지", answer: "정답 및 해설", audio: "듣기평가 음원", other: "기타 자료" };
const has = (o: object, k: string) => Object.prototype.hasOwnProperty.call(o, k);

type ExamMeta = { year: string; grade: string; examType: string; date: string; dateEnd: string; area: string };

// 저장된 과목 문자열("2025학년도 고등학교 1학년 3월 전국연합학력평가 (응시일 2025-03-01) / 국어 영역")을 분해한다.
const parseSubject = (v: unknown): ExamMeta | null => {
  const raw = String(v ?? "").trim();
  let m = raw.match(/^(\d{4})학년도\s+고등학교\s*([123])학년\s+(.+?)(?:\s*\(응시일\s*(\d{4}-\d{2}-\d{2})(?:\s*~\s*(\d{4}-\d{2}-\d{2}))?\))?\s+[\/·]\s+(.+)$/);
  if (m) return { year: m[1], grade: m[2], examType: m[3].trim(), date: m[4] ?? "", dateEnd: m[5] ?? "", area: m[6].trim() };
  m = raw.match(/^(\d{4})학년도\s+(.+?)(?:\s*\(응시일\s*(\d{4}-\d{2}-\d{2})(?:\s*~\s*(\d{4}-\d{2}-\d{2}))?\))?\s+[\/·]\s+(.+)$/);
  if (m) return { year: m[1], grade: "", examType: m[2].trim(), date: m[3] ?? "", dateEnd: m[4] ?? "", area: m[5].trim() };
  return null;
};
// 시험, 영역을 식별하는 키(응시 일자 제외). 등급 기준과 시험 자료는 이 키 단위로 한 번만 등록하여 모든 응시 회차가 공유한다.
const examKey = (subject: unknown) => {
  const m = parseSubject(subject);
  return m ? `${m.year}|${m.grade}|${m.examType}|${m.area}` : `raw|${String(subject ?? "")}`;
};
// 응시 회차 판정: 같은 시험(학년도, 학년, 시험 종류)의 응시 일자를 가까운 순으로 묶는다.
// 한 회차의 처음 응시 일자로부터 7일 이내의 일자는 같은 회차로 보며, 석차와 응시 인원은 회차, 영역 단위로 산출한다.
const DAY_MS = 86400000;
const SITTING_SPAN_DAYS = 7;
const dayNum = (d: string) => /^\d{4}-\d{2}-\d{2}$/.test(d) ? Date.parse(d + "T00:00:00Z") / DAY_MS : NaN;
const examOnlyKey = (m: ExamMeta) => `${m.year}|${m.grade}|${m.examType}`;
function sittingResolver(subjects: unknown[]) {
  const dates = new Map<string, Set<number>>();
  for (const sub of subjects) {
    const m = parseSubject(sub); if (!m) continue;
    const n = dayNum(m.date); if (!Number.isFinite(n)) continue;
    const k = examOnlyKey(m);
    if (!dates.has(k)) dates.set(k, new Set());
    dates.get(k)!.add(n);
  }
  const starts = new Map<string, Map<number, number>>();
  for (const [k, set] of dates) {
    const map = new Map<number, number>();
    let start = -Infinity;
    for (const n of [...set].sort((x, y) => x - y)) { if (n - start > SITTING_SPAN_DAYS) start = n; map.set(n, start); }
    starts.set(k, map);
  }
  return (subject: unknown) => {
    const m = parseSubject(subject);
    if (!m) return `raw|${String(subject ?? "")}`;
    const n = dayNum(m.date);
    const st = Number.isFinite(n) ? starts.get(examOnlyKey(m))?.get(n) : undefined;
    return `${examOnlyKey(m)}|${st === undefined ? "" : st}|${m.area}`;
  };
}
// 같은 시험, 영역이면서 응시 일자가 7일 이내이면 같은 응시 회차로 본다. (성적 중복 판정)
const sameSitting = (a: unknown, b: unknown) => {
  const x = parseSubject(a), y = parseSubject(b);
  if (!x || !y) return String(a) === String(b);
  if (examOnlyKey(x) !== examOnlyKey(y) || x.area !== y.area) return false;
  const dx = dayNum(x.date), dy = dayNum(y.date);
  if (!Number.isFinite(dx) || !Number.isFinite(dy)) return x.date === y.date;
  return Math.abs(dx - dy) <= SITTING_SPAN_DAYS;
};
const metaColumns = (m: ExamMeta) => ({ academic_year: m.year, school_grade: m.grade, exam_type: m.examType, exam_date: m.date || null, area: m.area });
// 저장 시 요구되는 시험 정보 검증
const validateWritableSubject = (subject: unknown, requireDate = true): { meta?: ExamMeta; error?: string } => {
  const m = parseSubject(subject);
  if (!m || !/^20\d{2}$/.test(m.year) || !["1", "2", "3"].includes(m.grade) || !has(TYPE_CODES, m.examType)) {
    return { error: "시험 정보의 형식이 올바르지 않습니다. 학년도, 학년, 시험 종류, 응시 일자, 영역을 확인하여 주시기 바랍니다." };
  }
  if (["1", "2"].includes(m.grade) && !LOWER_GRADE_CODES.includes(TYPE_CODES[m.examType])) return { error: "고등학교 1, 2학년에서 시행하지 않는 시험 종류입니다." };
  if (requireDate && !/^\d{4}-\d{2}-\d{2}$/.test(m.date)) return { error: "응시 일자를 입력하여 주시기 바랍니다." };
  if (m.dateEnd) return { error: "응시 일자는 하루만 입력할 수 있습니다. 영역마다 실제 응시한 날짜를 입력하여 주시기 바랍니다." };
  if (!requireDate && (m.date || m.dateEnd)) return { error: "등급 기준은 응시 일자 없이 시험, 영역 단위로 등록하여야 합니다." };
  if (!Object.values(AREA_LABELS).includes(m.area)) return { error: "영역이 올바르지 않습니다." };
  return { meta: m };
};

// ---------------------------------------------------------------------------
// 시험 자료 파일 처리
// ---------------------------------------------------------------------------
const parseGroup = (name: string) => {
  let m = name.match(/^y(20\d{2})-g([123])-m(\d{2})-t(3n|5n|6m|6n|7n|9m|9n|10n|11s)-a([a-z-]+)-c(paper|answer|audio)$/);
  if (m) return { year: m[1], grade: m[2], month: m[3], typeCode: m[4], area: m[5], category: m[6] };
  m = name.match(/^y(20\d{2})-g([123])-m(\d{2})-a([a-z-]+)-c(paper|answer|audio|other)$/);
  if (m) return { year: m[1], grade: m[2], month: m[3], typeCode: `${Number(m[3])}n`, area: m[4], category: m[5] };
  return null;
};
const displayNameFromStored = (storedName: string) => {
  const match = storedName.match(/^[0-9a-f-]{36}-([A-Za-z0-9_-]+)\.(mp3|pdf|hwp|hwpx)$/i);
  if (!match) return storedName;
  try {
    const raw = atob(match[1].replace(/-/g, "+").replace(/_/g, "/") + "=".repeat((4 - match[1].length % 4) % 4));
    return new TextDecoder().decode(Uint8Array.from(raw, c => c.charCodeAt(0)));
  } catch {
    return storedName;
  }
};
const describePath = (path: string) => {
  const bits = String(path).split("/");
  const g = parseGroup(bits[0] ?? "");
  const name = displayNameFromStored(bits[bits.length - 1] ?? "");
  if (!g) return name;
  return `${g.year}학년도 고등학교 ${g.grade}학년 ${TYPE_LABELS[g.typeCode] ?? ""} / ${AREA_LABELS_LEGACY[g.area] ?? g.area} / ${CATEGORY_LABELS[g.category] ?? g.category} / ${name}`;
};
const validPath = (path: string) => !!path && !path.includes("..") && /\.(mp3|pdf|hwp|hwpx)$/i.test(path);

// 파일 메타 정보(학년도, 학년, 시험 종류, 응시 일자, 영역, 자료 종류) 검증
const validateFileMeta = (body: any) => {
  const category = ["paper", "answer", "audio"].includes(String(body.category)) ? String(body.category) : "";
  if (!category) return { error: "자료 종류를 선택하여 주시기 바랍니다." };
  const year = /^20\d{2}$/.test(String(body.academicYear)) ? String(body.academicYear) : "";
  const grade = ["1", "2", "3"].includes(String(body.schoolGrade)) ? String(body.schoolGrade) : "";
  const examType = String(body.examType ?? "").trim();
  if (!year || !grade || !has(TYPE_CODES, examType)) return { error: "학년도, 학년, 시험 종류를 선택하여 주시기 바랍니다." };
  const typeCode = TYPE_CODES[examType];
  if (["1", "2"].includes(grade) && !LOWER_GRADE_CODES.includes(typeCode)) return { error: "고등학교 1, 2학년에서 시행하지 않는 시험 종류입니다." };
  const area = String(body.subjectArea ?? "");
  if (!has(AREA_LABELS, area)) return { error: "영역을 선택하여 주시기 바랍니다." };
  const month = String(examType.match(/^(\d+)월/)?.[1] ?? "3").padStart(2, "0");
  // 시험 자료는 시험, 영역 단위로 관리하므로 응시 일자를 요구하지 않는다. (기존 자료의 날짜 폴더는 그대로 유지)
  const date = /^\d{4}-\d{2}-\d{2}$/.test(String(body.examDate ?? "")) ? String(body.examDate) : "undated";
  return { category, year, grade, examType, typeCode, month, date, area, group: `y${year}-g${grade}-m${month}-t${typeCode}-a${area}-c${category}` };
};

async function listExamFiles(db: any, accept?: (g: { year: string; grade: string; typeCode: string; area: string; date: string }, groupOnly?: boolean) => boolean) {
  const { data: bucketInfo, error: bucketError } = await db.storage.getBucket(BUCKET);
  if (bucketError || !bucketInfo) return { files: [] as any[] };
  const { data: groups, error } = await db.storage.from(BUCKET).list("", { limit: 1000, sortBy: { column: "name", order: "asc" } });
  if (error) return { files: [] as any[], error: String(error.message) };
  const files: any[] = [];
  const targets = (groups ?? []).filter((g: any) => g.id === null && !g.metadata).map((g: any) => ({ g, p: parseGroup(g.name) }))
    .filter((x: any) => x.p && !(["1", "2"].includes(x.p.grade) && !LOWER_GRADE_CODES.includes(x.p.typeCode)))
    .filter((x: any) => !accept || accept({ year: x.p.year, grade: x.p.grade, typeCode: x.p.typeCode, area: x.p.area, date: "" }, true));
  // 분류 폴더와 날짜 폴더를 순차로 읽으면 느려지므로 일정 개수씩 병렬로 조회한다.
  for (const part of chunk(targets, 8)) {
    await Promise.all(part.map(async ({ g, p }: any) => {
      const { data: dates } = await db.storage.from(BUCKET).list(g.name, { limit: 1000 });
      await Promise.all((dates ?? []).filter((d: any) => d.id === null && !d.metadata).map(async (d: any) => {
        if (accept && !accept({ year: p.year, grade: p.grade, typeCode: p.typeCode, area: p.area, date: d.name })) return;
        const { data: children } = await db.storage.from(BUCKET).list(`${g.name}/${d.name}`, { limit: 1000, sortBy: { column: "created_at", order: "desc" } });
        for (const f of children ?? []) {
          if (!f.id || !/\.(mp3|pdf|hwp|hwpx)$/i.test(f.name)) continue;
          files.push({
            path: `${g.name}/${d.name}/${f.name}`,
            name: displayNameFromStored(f.name),
            category: CATEGORY_LABELS[p.category],
            academic_year: p.year,
            school_grade: p.grade,
            exam_month: Number(p.month),
            exam_type: TYPE_LABELS[p.typeCode] || `${Number(p.month)}월 전국연합학력평가`,
            exam_date: d.name === "undated" ? "" : d.name,
            subject_area: AREA_LABELS_LEGACY[p.area] || p.area,
            size: f.metadata?.size ?? 0,
            created_at: f.created_at,
          });
        }
      }));
    }));
  }
  return { files };
}

// 파일 접근 권한 키: 학생이 응시한 시험, 영역의 자료만 열람할 수 있다.
const accessKeyOf = (subject: unknown) => {
  const m = parseSubject(subject);
  if (!m || !has(TYPE_CODES, m.examType) || !has(AREA_CODES, m.area)) return null;
  return `${m.year}|${m.grade}|${TYPE_CODES[m.examType]}|${AREA_CODES[m.area]}`;
};

async function signedDownload(db: any, path: string) {
  const downloadName = displayNameFromStored(path.split("/").pop() ?? "");
  const { data, error } = await db.storage.from(BUCKET).createSignedUrl(path, 60 * 60);
  if (error || !data?.signedUrl) return null;
  // download 파라미터를 직접 한 번만 인코딩하여, 업로드한 원래 파일명 그대로 저장되도록 한다.
  const url = data.signedUrl + (data.signedUrl.includes("?") ? "&" : "?") + "download=" + encodeURIComponent(downloadName);
  return { url, name: downloadName };
}

// ---------------------------------------------------------------------------
// 정답 및 배점 / 정답 채점
// ---------------------------------------------------------------------------
type AnswerItem = { ans: string; pts: number };
async function findAnswerKey(db: any, m: ExamMeta, variant: string): Promise<{ id: any; variant: string; items: AnswerItem[] } | null> {
  const r = await db.from("answer_keys").select("id,variant,items").eq("academic_year", m.year).eq("school_grade", m.grade).eq("exam_type", m.examType).eq("area", m.area).eq("variant", variant).maybeSingle();
  if (r.error || !r.data || !Array.isArray(r.data.items)) return null;
  return { id: r.data.id, variant: String(r.data.variant ?? ""), items: r.data.items as AnswerItem[] };
}
const sanitizeAnswers = (a: unknown, len: number): string[] => {
  const arr = Array.isArray(a) ? a : [];
  return Array.from({ length: len }, (_, i) => String(arr[i] ?? "").replace(/[^0-9]/g, "").slice(0, 6));
};
// 학생이 마킹한 답이 정답(복수 정답 포함)과 일치하는 문항의 배점을 합산한다. 빈칸은 오답으로 처리한다.
const gradeAnswers = (items: AnswerItem[], a: string[]) => {
  let sum = 0;
  items.forEach((it, i) => {
    const given = String(a[i] ?? "").trim();
    if (!given) return;
    if (String(it.ans).split(",").map(x => x.trim()).includes(given)) sum += Number(it.pts);
  });
  return Math.round(sum * 10) / 10;
};
async function regradeScores(db: any, m: ExamMeta, variant: string, items: AnswerItem[]) {
  const r = await fetchAll((a, b) => db.from("scores").select("id,score,answers").eq("academic_year", m.year).eq("school_grade", m.grade).eq("exam_type", m.examType).eq("area", m.area).not("answers", "is", null).order("id").range(a, b));
  if (r.error) return { regraded: 0, changed: 0, failed: true };
  const targets = (r.data ?? []).filter((x: any) => String(x.answers?.variant ?? "") === variant);
  let changed = 0;
  for (const part of chunk(targets, 10)) {
    await Promise.all(part.map(async (x: any) => {
      const n = gradeAnswers(items, sanitizeAnswers(x.answers?.a, items.length));
      if (Math.abs(n - Number(x.score)) > 1e-9) { const u = await db.from("scores").update({ score: n }).eq("id", x.id); if (!u.error) changed++; }
    }));
  }
  return { regraded: targets.length, changed, failed: false };
}

// ---------------------------------------------------------------------------
// 자동 백업: 관리자가 데이터를 변경하는 첫 요청이 있는 날마다 한 번, 변경 직전의 상태를 비공개 저장소에 JSON으로 보관한다.
// ---------------------------------------------------------------------------
const BACKUP_BUCKET = "mock-exam-backups";
const BACKUP_KEEP = 30;
const WRITE_ACTIONS = new Set(["save_student", "delete_student", "save_score", "delete_score", "bulk_scores", "save_cutoff", "save_cutoffs", "delete_cutoff", "save_answer_key", "delete_answer_key", "set_publication"]);
const kstStamp = () => new Date(Date.now() + 9 * 3600 * 1000).toISOString().slice(0, 19).replace(/[T:]/g, "-");
let lastAutoBackupDay = "";
async function makeBackup(db: any) {
  const b = await db.storage.getBucket(BACKUP_BUCKET);
  if (b.error || !b.data) {
    const c = await db.storage.createBucket(BACKUP_BUCKET, { public: false });
    if (c.error && !/already exists|duplicate/i.test(String(c.error.message))) throw new Error("백업 저장소를 준비하지 못하였습니다: " + c.error.message);
  }
  const tables: Record<string, any[]> = {};
  for (const t of ["students", "scores", "grade_cutoffs", "answer_keys"]) {
    const r = await fetchAll((a, z) => db.from(t).select("*").order("id").range(a, z));
    if (r.error) throw new Error(`${t} 테이블을 읽지 못하였습니다.`);
    tables[t] = r.data ?? [];
  }
  const name = `${kstStamp()}.json`;
  const body = JSON.stringify({ version: SYSTEM_VERSION, created_at: new Date().toISOString(), counts: Object.fromEntries(Object.entries(tables).map(([k, v]) => [k, v.length])), tables });
  const up = await db.storage.from(BACKUP_BUCKET).upload(name, new Blob([body], { type: "application/json" }), { contentType: "application/json", upsert: false });
  if (up.error) throw new Error("백업 파일을 저장하지 못하였습니다: " + up.error.message);
  const list = await db.storage.from(BACKUP_BUCKET).list("", { limit: 1000, sortBy: { column: "name", order: "desc" } });
  const old = (list.data ?? []).filter((f: any) => /^\d{4}(-\d{2}){5}\.json$/.test(f.name)).slice(BACKUP_KEEP).map((f: any) => f.name);
  if (old.length) await db.storage.from(BACKUP_BUCKET).remove(old);
  return { name, size: body.length, counts: Object.fromEntries(Object.entries(tables).map(([k, v]) => [k, v.length])) };
}
async function autoBackup(db: any, audit: (a: string, s: string) => Promise<void>) {
  const day = kstStamp().slice(0, 10);
  if (lastAutoBackupDay === day) return;
  try {
    const list = await db.storage.from(BACKUP_BUCKET).list("", { limit: 100, search: day });
    if (!list.error && (list.data ?? []).some((f: any) => String(f.name).startsWith(day))) { lastAutoBackupDay = day; return; }
    const r = await makeBackup(db);
    lastAutoBackupDay = day;
    await audit("auto_backup", `자동 백업 완료: ${r.name}`);
  } catch (e) { console.error("auto backup failed", e); }
}

// ---------------------------------------------------------------------------
// 시스템 변경 내역: 코드가 수정되어 새 버전이 배포되면, 아래 내역이 작업 기록에 한 번만 자동으로 기록된다.
// 코드를 수정할 때에는 SYSTEM_VERSION을 새 값으로 바꾸고 SYSTEM_CHANGES에 변경 내용을 한글로 작성한다.
// ---------------------------------------------------------------------------
const SYSTEM_VERSION = "2026-10-28-02";
const SYSTEM_CHANGES: string[] = [
  "성적 관리 응시 일자 입력 개선: 학년도 및 시험 종류를 선택하더라도 응시 일자의 연도와 월이 자동으로 지정되지 않고, 현재 달력이 표시되도록 변경함.",
  "정답 및 배점 관리 개선: 선택과목 항목을 폐지하고, 영역별 기본 문항 수를 국어 45문항, 수학 30문항(선택형 21문항, 단답형 9문항), 영어 45문항, 사회탐구 25문항, 과학탐구 25문항으로 조정함. 선택형 문항의 정답은 1부터 5까지의 숫자로만 입력하도록 검증을 추가함.",
  "정답 및 배점 관리 입력 항목의 명칭과 안내 문구를 형식적 표현으로 통일하고, 입력 칸의 크기를 동일하게 정비함. 정답 저장 시 표시되던 복수 정답 안내 문구를 삭제함.",
  "성적 공개 관리 화면 정비: 공개 상태 표시에서 건수와 시간대 안내 문구를 삭제하고, 성적 관리 목록의 공개 상태 표시를 시험명 앞에 배치함.",
  "화면 문구 정비: 모든 화면 문구에서 가운뎃점 사용을 폐지하고 쉼표 및 형식적 표현으로 통일함. 사용자 안내 문장의 어투를 형식적 표현으로 정리함.",
];
let systemRecorded = false;
async function recordSystemUpdate(db: any) {
  if (systemRecorded) return;
  systemRecorded = true;
  try {
    const found = await db.from("admin_audit_log").select("id").eq("action", "system_update").eq("admin_code", SYSTEM_VERSION).limit(1);
    if (found.error) { systemRecorded = false; return; }
    if ((found.data ?? []).length) return;
    const base = Date.now();
    await db.from("admin_audit_log").insert(SYSTEM_CHANGES.map((summary, i) => ({ admin_code: SYSTEM_VERSION, admin_name: "시스템", action: "system_update", summary, created_at: new Date(base - i).toISOString() })));
  } catch { systemRecorded = false; }
}

// Supabase(PostgREST)는 한 번에 최대 1000행만 반환하므로, 전체 조회가 필요한 곳은 페이지 단위로 모두 읽는다.
async function fetchAll(build: (from: number, to: number) => any): Promise<{ data: any[] | null; error: any }> {
  const out: any[] = [];
  for (let from = 0; ; from += 1000) {
    const r = await build(from, from + 999);
    if (r.error) return { data: null, error: r.error };
    const rows = r.data ?? [];
    out.push(...rows);
    if (rows.length < 1000) break;
  }
  return { data: out, error: null };
}

function chunk<T>(arr: T[], size: number): T[][] {
  const out: T[][] = [];
  for (let i = 0; i < arr.length; i += size) out.push(arr.slice(i, i + size));
  return out;
}

// 학생 본인 확인 (시도 횟수 제한 포함)
async function verifyStudent(db: any, req: Request, sessionSecret: string, rawCode: unknown, rawBirth: unknown): Promise<{ student?: any; failure?: Response }> {
  const code = String(rawCode ?? "").trim().toUpperCase();
  const birthdate = String(rawBirth ?? "").trim();
  if (!/^M[A-Z0-9]{5}$/.test(code) || !/^\d{8}$/.test(birthdate)) return { failure: json({ error: "개인식별코드 또는 생년월일이 올바르지 않습니다." }, 400) };
  const ip = (req.headers.get("x-forwarded-for") ?? req.headers.get("cf-connecting-ip") ?? "unknown").split(",")[0].trim();
  const ipHash = b64url(new Uint8Array(await crypto.subtle.digest("SHA-256", enc.encode(`${ip}|student|${code}|${sessionSecret}`))));
  const now = Date.now();
  const { data: attempt } = await db.from("admin_login_attempts").select("failed_count,window_start,blocked_until").eq("ip_hash", ipHash).maybeSingle();
  if (attempt?.blocked_until && new Date(attempt.blocked_until).getTime() > now) return { failure: json({ error: "조회 시도 횟수가 제한을 초과하였습니다. 15분 후 다시 시도하여 주시기 바랍니다." }, 429) };
  const { data: student, error: studentError } = await db.from("students").select("id,student_code").eq("student_code", code).eq("birthdate", birthdate).maybeSingle();
  if (studentError || !student) {
    const withinWindow = attempt?.window_start && now - new Date(attempt.window_start).getTime() < 15 * 60 * 1000;
    const count = withinWindow ? Number(attempt.failed_count || 0) + 1 : 1;
    await db.from("admin_login_attempts").upsert({ ip_hash: ipHash, failed_count: count, window_start: withinWindow ? attempt.window_start : new Date(now).toISOString(), blocked_until: count >= 8 ? new Date(now + 15 * 60 * 1000).toISOString() : null }, { onConflict: "ip_hash" });
    return { failure: json({ error: count >= 8 ? "조회 시도 횟수가 제한을 초과하였습니다. 15분 후 다시 시도하여 주시기 바랍니다." : "개인식별코드 또는 생년월일이 올바르지 않습니다." }, count >= 8 ? 429 : 401) };
  }
  await db.from("admin_login_attempts").delete().eq("ip_hash", ipHash);
  return { student };
}

Deno.serve(async (req: Request) => {
  if (req.method === "OPTIONS") return new Response("ok", { headers: corsHeaders });
  if (req.method !== "POST") return json({ error: "POST 요청만 허용됩니다." }, 405);

  try {
    const url = Deno.env.get("SUPABASE_URL");
    const serviceKey = Deno.env.get("SUPABASE_SERVICE_ROLE_KEY");
    const sessionSecret = Deno.env.get("ADMIN_SESSION_SECRET");
    const accountsRaw = Deno.env.get("ADMIN_ACCOUNTS_JSON");
    if (!url || !serviceKey || !sessionSecret || !accountsRaw) {
      return json({ error: "관리자 서버 설정이 완료되지 않았습니다. Edge Function Secrets를 확인하시기 바랍니다." }, 500);
    }
    const db = createClient(url, serviceKey, { auth: { persistSession: false, autoRefreshToken: false } });
    const body: any = await req.json().catch(() => ({}));
    const action = String(body?.action ?? "");

    const writeAudit = async (adminCode: string, adminName: string, act: string, summary: string) => {
      try { await db.from("admin_audit_log").insert({ admin_code: adminCode, admin_name: adminName, action: act, summary: String(summary).slice(0, 500) }); } catch { /* 기록 실패가 업무를 중단시키지 않도록 한다. */ }
    };

    // Student lookup is public, but identity is checked on the server.
    if (action === "lookup_student") {
      const verified = await verifyStudent(db, req, sessionSecret, body.student_code, body.birthdate);
      if (verified.failure) return verified.failure;
      const student = verified.student;
      const ownRes = await db.from("scores").select("id,subject,score,published_at").eq("student_id", student.id).order("subject");
      if (ownRes.error) return json({ error: "성적 자료를 조회하지 못하였습니다." }, 500);
      const nowMs = Date.now();
      // 공개 시점이 지난 성적만 학생에게 보인다. (비공개, 예약 상태의 성적은 제외)
      const own = (ownRes.data ?? []).filter((x: any) => x.published_at && new Date(x.published_at).getTime() <= nowMs);
      // 석차, 응시 인원 산출에는 본인이 응시한 시험 전체의 성적이 필요하므로, 시험 단위로 병렬 조회한다.
      const examGroups = new Map<string, ExamMeta>();
      for (const x of own as any[]) { const m = parseSubject(x.subject); if (m) examGroups.set(examOnlyKey(m), m); }
      const [cohortParts, cutRes] = await Promise.all([
        Promise.all([...examGroups.values()].map(m => fetchAll((a, b) => db.from("scores").select("student_id,subject,score").eq("academic_year", m.year).eq("school_grade", m.grade).eq("exam_type", m.examType).order("id").range(a, b)))),
        fetchAll((a, b) => db.from("grade_cutoffs").select("subject,grade,min_score").order("id").range(a, b)),
      ]);
      if (cutRes.error || cohortParts.some((r: any) => r.error)) return json({ error: "성적 자료를 조회하지 못하였습니다." }, 500);
      const cuts = cutRes.data ?? [];
      const all = cohortParts.flatMap((r: any) => r.data ?? []);
      const resolveSitting = sittingResolver([...all.map((x: any) => x.subject), ...own.map((x: any) => x.subject)]);
      const cutoffRows = (cuts ?? []).filter((c: any) => !isEnglish(c.subject));
      const cohorts = new Map<string, number[]>();
      for (const x of all as any[]) {
        if (x.score === null || x.score === undefined || x.score === "" || !Number.isFinite(Number(x.score))) continue;
        const k = resolveSitting(x.subject);
        if (!cohorts.has(k)) cohorts.set(k, []);
        cohorts.get(k)!.push(Number(x.score));
      }
      const accessKeys = new Set<string>();
      const scores = own.map((s: any) => {
        const score = Number(s.score);
        if (s.score === null || s.score === undefined || s.score === "" || !Number.isFinite(score)) {
          return { subject: s.subject, score: null, rank: null, tie_count: null, participant_count: 0, average: null, grade: null, cutoffs: [], attendance_status: "absent", attendance_label: "미응시" };
        }
        const key = resolveSitting(s.subject);
        const baseKey = examKey(s.subject);
        const ak = accessKeyOf(s.subject);
        if (ak) accessKeys.add(ak);
        const nums = cohorts.get(key) ?? [];
        const rank = 1 + nums.filter((n: number) => n > score).length;
        const tieCount = nums.filter((n: number) => n === score).length;
        const average = nums.length ? nums.reduce((a: number, b: number) => a + b, 0) / nums.length : null;
        let subjectCuts: any[] = [];
        let grade: number | null = null;
        if (isEnglish(s.subject)) {
          grade = absoluteGrade(score, true);
        } else {
          const byGrade = new Map<number, any>();
          for (const c of cutoffRows as any[]) {
            if (examKey(c.subject) !== baseKey || Number(c.grade) > 8) continue;
            if (!byGrade.has(Number(c.grade))) byGrade.set(Number(c.grade), c);
          }
          subjectCuts = [...byGrade.values()].sort((a: any, b: any) => Number(a.grade) - Number(b.grade));
          const qualified = subjectCuts.filter((c: any) => score >= Number(c.min_score)).sort((a: any, b: any) => Number(a.grade) - Number(b.grade));
          grade = subjectCuts.length === 0 ? null : (qualified.length ? Number(qualified[0].grade) : 9);
        }
        return { subject: s.subject, score, rank, tie_count: tieCount, participant_count: nums.length, average, grade, cutoffs: subjectCuts, attendance_status: "attended", attendance_label: "응시" };
      });
      const fileResult = await listExamFiles(db, g => accessKeys.has(`${g.year}|${g.grade}|${g.typeCode}|${g.area}`));
      return json({ scores, files: fileResult.files });
    }

    // Student file download: identity and exam participation are verified on the server.
    if (action === "student_file_url") {
      const verified = await verifyStudent(db, req, sessionSecret, body.student_code, body.birthdate);
      if (verified.failure) return verified.failure;
      const path = String(body.path ?? "");
      const bits = path.split("/");
      if (!validPath(path) || bits.length !== 3) return json({ error: "파일 경로가 올바르지 않습니다." }, 400);
      const g = parseGroup(bits[0]);
      const { data: own, error: ownError } = await db.from("scores").select("subject,score").eq("student_id", verified.student.id);
      if (ownError) return json({ error: "성적 자료를 조회하지 못하였습니다." }, 500);
      const keys = new Set<string>();
      for (const s of own ?? []) {
        if (s.score === null || s.score === undefined || s.score === "" || !Number.isFinite(Number(s.score))) continue;
        const k = accessKeyOf(s.subject);
        if (k) keys.add(k);
      }
      if (!g || !keys.has(`${g.year}|${g.grade}|${g.typeCode}|${g.area}`)) return json({ error: "해당 파일에 대한 열람 권한이 없습니다." }, 403);
      const d = await signedDownload(db, path);
      if (!d) return json({ error: "다운로드 주소를 생성하지 못하였습니다." }, 404);
      return json(d);
    }

    // Admin sign-in uses the shared input screen; credentials remain server-side.
    if (action === "admin_login") {
      const code = String(body.admin_code ?? body.code ?? "").trim().toUpperCase();
      const birthdate = String(body.birthdate ?? "").trim();
      let accounts: Array<{ code: string; birthdate: string; name?: string }>;
      try { accounts = JSON.parse(accountsRaw); } catch { return json({ error: "관리자 계정 설정 형식이 올바르지 않습니다." }, 500); }
      const ip = (req.headers.get("x-forwarded-for") ?? req.headers.get("cf-connecting-ip") ?? "unknown").split(",")[0].trim();
      const ipHash = b64url(new Uint8Array(await crypto.subtle.digest("SHA-256", enc.encode(ip + sessionSecret))));
      const now = Date.now();
      const { data: attempt } = await db.from("admin_login_attempts").select("failed_count,window_start,blocked_until").eq("ip_hash", ipHash).maybeSingle();
      if (attempt?.blocked_until && new Date(attempt.blocked_until).getTime() > now) return json({ error: "인증 시도 횟수가 제한을 초과하였습니다. 잠시 후 다시 시도하여 주시기 바랍니다." }, 429);
      const matchedAdmin = accounts.find(a => String(a.code).trim().toUpperCase() === code && String(a.birthdate).trim() === birthdate);
      const valid = !!matchedAdmin;
      if (!valid) {
        const withinWindow = attempt?.window_start && now - new Date(attempt.window_start).getTime() < 15 * 60 * 1000;
        const count = withinWindow ? Number(attempt.failed_count || 0) + 1 : 1;
        const values = { ip_hash: ipHash, failed_count: count, window_start: withinWindow ? attempt.window_start : new Date(now).toISOString(), blocked_until: count >= 5 ? new Date(now + 15 * 60 * 1000).toISOString() : null };
        await db.from("admin_login_attempts").upsert(values, { onConflict: "ip_hash" });
        return json({ error: count >= 5 ? "인증 시도 횟수가 제한을 초과하였습니다. 15분 후 다시 시도하여 주시기 바랍니다." : "개인식별코드 또는 생년월일이 올바르지 않습니다." }, count >= 5 ? 429 : 401);
      }
      await db.from("admin_login_attempts").delete().eq("ip_hash", ipHash);
      const adminName = typeof matchedAdmin?.name === "string" ? matchedAdmin.name.trim() : "";
      const header = encodeJson({ alg: "HS256", typ: "JWT" });
      const payload = encodeJson({ sub: code, role: "admin", name: adminName, exp: Math.floor(now / 1000) + 2 * 60 * 60 });
      const unsigned = `${header}.${payload}`;
      const key = await crypto.subtle.importKey("raw", enc.encode(sessionSecret), { name: "HMAC", hash: "SHA-256" }, false, ["sign"]);
      const signature = new Uint8Array(await crypto.subtle.sign("HMAC", key, enc.encode(unsigned)));
      await recordSystemUpdate(db);
      await writeAudit(code, adminName, "admin_login", "관리자 로그인");
      return json({ token: `${unsigned}.${b64url(signature)}`, expires_in: 7200, admin_name: adminName });
    }

    // All management operations require a short-lived, server-signed token.
    const auth = req.headers.get("Authorization") ?? "";
    const token = auth.match(/^Bearer\s+(.+)$/i)?.[1] ?? "";
    const parts = token.split(".");
    if (parts.length !== 3) return json({ error: "관리자 인증이 필요합니다." }, 401);
    const unsigned = `${parts[0]}.${parts[1]}`;
    const key = await crypto.subtle.importKey("raw", enc.encode(sessionSecret), { name: "HMAC", hash: "SHA-256" }, false, ["verify"]);
    const validSig = await crypto.subtle.verify("HMAC", key, fromB64url(parts[2]), enc.encode(unsigned));
    let claims: any;
    try { claims = JSON.parse(new TextDecoder().decode(fromB64url(parts[1]))); } catch { claims = null; }
    if (!validSig || claims?.role !== "admin" || !claims?.sub || Number(claims.exp) <= Math.floor(Date.now() / 1000)) return json({ error: "관리자 인증이 만료되었거나 유효하지 않습니다." }, 401);

    const adminCode = String(claims.sub);
    const adminDisplay = String(claims.name ?? "");
    const audit = (act: string, summary: string) => writeAudit(adminCode, adminDisplay, act, summary);
    const studentCodeOf = async (id: unknown) => {
      const r = await db.from("students").select("student_code").eq("id", id).maybeSingle();
      return String(r.data?.student_code ?? id ?? "");
    };

    if (WRITE_ACTIONS.has(action)) await autoBackup(db, audit);

    switch (action) {
      case "create_exam_upload": {
        // 파일 본문은 Edge Function을 거치지 않고, 발급된 서명 URL로 브라우저가 Storage에 직접 업로드한다.
        const originalName = String(body.fileName ?? "").replace(/[\\/\0-\x1f]/g, "_").trim();
        const ext = originalName.split(".").pop()?.toLowerCase() ?? "";
        if (!originalName || !["mp3", "pdf", "hwp", "hwpx"].includes(ext)) return json({ error: "MP3, PDF, HWP, HWPX 파일만 업로드할 수 있습니다." }, 400);
        const size = Number(body.fileSize);
        if (!Number.isFinite(size) || size < 1 || size > 500 * 1024 * 1024) return json({ error: "파일 크기는 1바이트 이상 500MB 이하여야 합니다." }, 400);
        const meta: any = validateFileMeta(body);
        if (meta.error) return json({ error: meta.error }, 400);
        const { data: bucketInfo, error: bucketError } = await db.storage.getBucket(BUCKET);
        if (bucketError || !bucketInfo) {
          const created = await db.storage.createBucket(BUCKET, { public: false });
          if (created.error && !/already exists|duplicate/i.test(String(created.error.message))) {
            const verify = await db.storage.getBucket(BUCKET);
            if (verify.error || !verify.data) return json({ error: "파일 저장소를 준비하지 못하였습니다. Supabase Storage에서 'mock-exam-files' 비공개 버킷을 생성하여 주시기 바랍니다. 상세 오류: " + created.error.message }, 500);
          }
        }
        const path = `${meta.group}/${meta.date}/${crypto.randomUUID()}-${b64url(enc.encode(originalName))}.${ext}`;
        const { data, error } = await db.storage.from(BUCKET).createSignedUploadUrl(path);
        if (error || !data?.signedUrl) return json({ error: "업로드 주소를 생성하지 못하였습니다." }, 500);
        return json({ path, signedUrl: data.signedUrl, name: originalName });
      }
      case "confirm_exam_upload": {
        const path = String(body.path ?? "");
        const bits = path.split("/");
        if (!validPath(path) || bits.length !== 3 || !parseGroup(bits[0])) return json({ error: "파일 경로가 올바르지 않습니다." }, 400);
        const { data, error } = await db.storage.from(BUCKET).list(`${bits[0]}/${bits[1]}`, { limit: 100, search: bits[2] });
        if (error || !(data ?? []).some((f: any) => f.name === bits[2])) return json({ error: "업로드된 파일을 확인하지 못하였습니다." }, 404);
        await audit("upload_exam_file", `파일 업로드: ${describePath(path)}`);
        return json({ success: true });
      }
      case "list_exam_files": {
        const r = await listExamFiles(db);
        if (r.error) return json({ error: "파일 목록을 불러오지 못하였습니다: " + r.error }, 400);
        return json({ files: r.files.sort((a, b) => String(b.created_at ?? "").localeCompare(String(a.created_at ?? ""))) });
      }
      case "get_exam_file_url": {
        const path = String(body.path ?? "");
        if (!validPath(path)) return json({ error: "파일 경로가 올바르지 않습니다." }, 400);
        const d = await signedDownload(db, path);
        if (!d) return json({ error: "다운로드 주소를 생성하지 못하였습니다." }, 404);
        await audit("download_exam_file", `파일 다운로드: ${describePath(path)}`);
        return json(d);
      }
      case "update_exam_file_category": {
        const path = String(body.path ?? "");
        const category = String(body.category ?? "");
        if (!validPath(path) || !["paper", "answer", "audio"].includes(category)) return json({ error: "파일 경로 또는 자료 종류가 올바르지 않습니다." }, 400);
        const bits = path.split("/");
        const group = bits[0];
        if (!/^y20\d{2}-g[123]-m\d{2}-t(3n|5n|6m|6n|7n|9m|9n|10n|11s)-a[a-z-]+-c(paper|answer|audio)$/.test(group)) return json({ error: "파일 분류 경로를 확인할 수 없습니다." }, 400);
        const current = group.match(/-c(paper|answer|audio)$/)?.[1];
        if (current === category) return json({ success: true, unchanged: true });
        const newGroup = group.replace(/-c(paper|answer|audio)$/, `-c${category}`);
        const newPath = [newGroup, ...bits.slice(1)].join("/");
        const { error } = await db.storage.from(BUCKET).move(path, newPath);
        if (error) return json({ error: "자료 종류를 수정하지 못하였습니다: " + error.message }, 400);
        await audit("update_exam_file", `파일 정보 수정: ${describePath(path)} → ${describePath(newPath)}`);
        return json({ success: true, path: newPath, category });
      }
      case "update_exam_file": {
        const path = String(body.path ?? "");
        if (!validPath(path)) return json({ error: "파일 경로가 올바르지 않습니다." }, 400);
        const bits = path.split("/");
        if (bits.length !== 3 || !parseGroup(bits[0])) return json({ error: "파일 분류 경로를 확인할 수 없습니다." }, 400);
        const meta: any = validateFileMeta(body);
        if (meta.error) return json({ error: meta.error }, 400);
        const newPath = `${meta.group}/${bits[1]}/${bits[2]}`;
        if (newPath === path) return json({ success: true, unchanged: true, path });
        const { error } = await db.storage.from(BUCKET).move(path, newPath);
        if (error) return json({ error: "파일 정보를 수정하지 못하였습니다: " + error.message }, 400);
        await audit("update_exam_file", `파일 정보 수정: ${describePath(path)} → ${describePath(newPath)}`);
        return json({ success: true, path: newPath });
      }
      case "rename_exam_file": {
        const path = String(body.path ?? "");
        const name = String(body.name ?? "").trim().replace(/[\\/\0-\x1f]/g, "_");
        if (!path || path.includes("..") || !name || !/\.(mp3|pdf|hwp|hwpx)$/i.test(path) || name.split(".").pop()?.toLowerCase() !== path.split(".").pop()?.toLowerCase()) return json({ error: "파일명 또는 확장자가 올바르지 않습니다." }, 400);
        const bits = path.split("/");
        bits.pop();
        const encodedName = b64url(enc.encode(name));
        const newPath = [...bits, `${crypto.randomUUID()}-${encodedName}.${name.split(".").pop()!.toLowerCase()}`].join("/");
        const { error } = await db.storage.from(BUCKET).move(path, newPath);
        if (error) return json({ error: "파일명을 수정하지 못하였습니다: " + error.message }, 400);
        await audit("rename_exam_file", `파일명 수정: ${describePath(path)} → ${name}`);
        return json({ success: true, path: newPath, name });
      }
      case "delete_exam_file": {
        const path = String(body.path ?? "");
        if (!validPath(path)) return json({ error: "파일 경로가 올바르지 않습니다." }, 400);
        const { error } = await db.storage.from(BUCKET).remove([path]);
        if (error) return json({ error: "파일을 삭제하지 못하였습니다: " + error.message }, 400);
        await audit("delete_exam_file", `파일 삭제: ${describePath(path)}`);
        return json({ success: true });
      }
      case "dashboard": {
        const [s, c, g, k] = await Promise.all([
          fetchAll((a, b) => db.from("students").select("id,student_code,birthdate").order("student_code").order("id").range(a, b)),
          fetchAll((a, b) => db.from("scores").select("id,student_id,subject,score,published_at,answers").order("subject").order("id").range(a, b)),
          fetchAll((a, b) => db.from("grade_cutoffs").select("id,subject,grade,min_score").order("subject").order("grade").order("id").range(a, b)),
          fetchAll((a, b) => db.from("answer_keys").select("id,academic_year,school_grade,exam_type,area,variant,items").order("id").range(a, b)),
        ]);
        if (s.error || c.error || g.error || k.error) return json({ error: "관리 데이터를 불러오지 못하였습니다. migration.sql 및 SCHEMA_NOTES.sql의 테이블 설정을 확인하시기 바랍니다." }, 500);
        return json({ students: s.data ?? [], scores: c.data ?? [], answer_keys: k.data ?? [], cutoffs: (g.data ?? []).filter((cut: any) => !isEnglish(cut.subject) && Number(cut.grade) <= 8) });
      }
      case "audit_log": {
        await recordSystemUpdate(db);
        const r = await db.from("admin_audit_log").select("id,created_at,admin_code,admin_name,action,summary").order("created_at", { ascending: false }).limit(300);
        if (r.error) return json({ error: "작업 기록을 불러오지 못하였습니다. migration.sql을 실행하였는지 확인하시기 바랍니다." }, 500);
        return json({ logs: r.data ?? [] });
      }
      case "save_student": {
        const s = body.student;
        const code = String(s?.student_code ?? "").trim().toUpperCase();
        const birthdate = String(s?.birthdate ?? "").trim();
        if (!/^M[A-Z0-9]{5}$/.test(code) || !/^\d{8}$/.test(birthdate)) return json({ error: "개인식별코드는 M으로 시작하는 영문, 숫자 6자리, 생년월일은 숫자 8자리여야 합니다." }, 400);
        const payload = { student_code: code, birthdate };
        const r = s.id ? await db.from("students").update(payload).eq("id", s.id).select("id").maybeSingle() : await db.from("students").insert(payload).select("id").single();
        if (r.error) return json({ error: "학생 정보를 저장하지 못하였습니다. 코드 중복 여부를 확인하여 주시기 바랍니다." }, 400);
        if (!r.data) return json({ error: "학생을 찾지 못하였습니다." }, 404);
        await audit("save_student", `학생 ${s.id ? "수정" : "등록"}: ${code}`);
        return json({ student: r.data });
      }
      case "delete_student": {
        const id = String(body.id ?? ""); if (!id) return json({ error: "학생 ID가 필요합니다." }, 400);
        const code = await studentCodeOf(id);
        const c = await db.from("scores").delete().eq("student_id", id); if (c.error) return json({ error: "연결된 성적을 삭제하지 못하였습니다." }, 400);
        const r = await db.from("students").delete().eq("id", id).select("id").maybeSingle(); if (r.error || !r.data) return json({ error: "학생을 삭제하지 못하였습니다." }, 400);
        await audit("delete_student", `학생 삭제: ${code} (연결된 성적 포함)`);
        return json({ success: true });
      }
      case "save_score": {
        const s = body.score;
        const subject = String(s?.subject ?? "").trim();
        if (!s?.student_id || !subject || subject.length > 160) return json({ error: "학생 또는 과목명을 확인하여 주시기 바랍니다." }, 400);
        const v = validateWritableSubject(subject);
        if (v.error || !v.meta) return json({ error: v.error }, 400);
        const maxScore = maxScoreForSubject(subject);
        let n = Number(s?.score);
        let answersToStore: any = null;
        let touchAnswers = true;
        if (s?.answers) {
          // 정답 채점: 서버가 등록된 정답, 배점으로 원점수를 다시 계산하며, 화면에서 전달된 점수는 사용하지 않는다.
          const keyRow = await findAnswerKey(db, v.meta, String(s.answers.variant ?? ""));
          if (!keyRow) return json({ error: "해당 시험, 영역의 정답이 등록되어 있지 않습니다. 정답 관리에서 먼저 등록하여 주시기 바랍니다." }, 400);
          const a = sanitizeAnswers(s.answers.a, keyRow.items.length);
          n = gradeAnswers(keyRow.items, a);
          answersToStore = { variant: keyRow.variant, a };
        } else if (s?.keep_answers && s?.id) {
          const prev = await db.from("scores").select("id,subject,score,answers").eq("id", s.id).maybeSingle();
          if (prev.error || !prev.data?.answers) return json({ error: "기존 답안 기록을 확인하지 못하였습니다." }, 400);
          if (examKey(prev.data.subject) !== examKey(subject)) return json({ error: "정답 채점으로 입력한 성적은 시험 종류와 영역을 변경할 수 없습니다. 채점 화면에서 다시 입력하여 주시기 바랍니다." }, 400);
          n = Number(prev.data.score);
          touchAnswers = false;
        } else if (!validScore(n, maxScore) || String(s.score ?? "").trim() === "") {
          return json({ error: `0~${maxScore}점 사이의 원점수(소수점 첫째 자리까지)를 확인하여 주시기 바랍니다.` }, 400);
        }
        if (!validScore(n, maxScore)) return json({ error: `원점수는 0~${maxScore}점 사이여야 합니다.` }, 400);
        const siblings = await db.from("scores").select("id,subject").eq("student_id", s.student_id);
        if (siblings.error) return json({ error: "성적을 저장하지 못하였습니다." }, 500);
        if ((siblings.data ?? []).some((x: any) => String(x.id) !== String(s.id ?? "") && sameSitting(x.subject, subject))) return json({ error: "동일한 학생, 시험, 영역의 성적이 이미 등록되어 있습니다." }, 409);
        const record: any = { student_id: s.student_id, subject, score: n, ...metaColumns(v.meta) };
        if (touchAnswers) record.answers = answersToStore;
        const r = s.id ? await db.from("scores").update(record).eq("id", s.id).select("id").maybeSingle() : await db.from("scores").insert(record).select("id").single();
        if (r.error || !r.data) return json({ error: "성적을 저장하지 못하였습니다." }, 400);
        await audit("save_score", `성적 ${s.id ? "수정" : "등록"}: ${await studentCodeOf(s.student_id)} / ${subject} / ${n}점${answersToStore ? " (정답 채점)" : ""}${s.id ? "" : " / 비공개"}`);
        return json({ score: r.data, computed_score: n });
      }
      case "delete_score": {
        const id = String(body.id ?? ""); if (!id) return json({ error: "성적 ID가 필요합니다." }, 400);
        const prev = await db.from("scores").select("student_id,subject,score").eq("id", id).maybeSingle();
        const r = await db.from("scores").delete().eq("id", id).select("id").maybeSingle(); if (r.error || !r.data) return json({ error: "성적을 삭제하지 못하였습니다." }, 400);
        await audit("delete_score", prev.data ? `성적 삭제: ${await studentCodeOf(prev.data.student_id)} / ${prev.data.subject} / ${prev.data.score}점` : `성적 삭제: ${id}`);
        return json({ success: true });
      }
      case "bulk_scores": {
        if (!Array.isArray(body.records) || body.records.length < 1 || body.records.length > 1000) return json({ error: "한 번에 1~1000개 행까지 입력할 수 있습니다." }, 400);
        type Row = { line: number; code: string; birth: string; subject: string; meta: ExamMeta; n: number };
        const errors: { line: number; reason: string }[] = [];
        const rows: Row[] = [];
        body.records.forEach((r: any, idx: number) => {
          const lineNo = Number(r?.line);
          const line = Number.isInteger(lineNo) && lineNo > 0 ? lineNo : idx + 1;
          const code = String(r?.student_code ?? "").toUpperCase(), birth = String(r?.birthdate ?? ""), subject = String(r?.subject ?? "").trim(), n = Number(r?.score);
          if (!/^M[A-Z0-9]{5}$/.test(code)) { errors.push({ line, reason: "개인식별코드의 형식이 올바르지 않습니다." }); return; }
          if (!/^\d{8}$/.test(birth)) { errors.push({ line, reason: "생년월일은 숫자 8자리여야 합니다." }); return; }
          if (!subject || subject.length > 160) { errors.push({ line, reason: "시험 정보가 올바르지 않습니다." }); return; }
          const v = validateWritableSubject(subject);
          if (v.error || !v.meta) { errors.push({ line, reason: v.error ?? "시험 정보가 올바르지 않습니다." }); return; }
          const maxScore = maxScoreForSubject(subject);
          if (r?.score === null || r?.score === undefined || String(r.score).trim() === "" || !validScore(n, maxScore)) { errors.push({ line, reason: `원점수는 0점 이상 ${maxScore}점 이하의 숫자(소수점 첫째 자리까지)여야 합니다.` }); return; }
          rows.push({ line, code, birth, subject, meta: v.meta, n });
        });
        const codes = [...new Set(rows.map(r => r.code))];
        const identities = new Map<string, any>();
        for (const part of chunk(codes, 200)) {
          const sr = await db.from("students").select("id,student_code,birthdate").in("student_code", part);
          if (sr.error) return json({ error: "학생 목록을 조회하지 못하였습니다." }, 500);
          for (const st of sr.data ?? []) identities.set(`${st.student_code}|${st.birthdate}`, st);
        }
        const resolved = new Map<string, { row: Row; student: any }>();
        for (const row of rows) {
          const st = identities.get(`${row.code}|${row.birth}`);
          if (!st) { errors.push({ line: row.line, reason: "등록된 학생 정보(개인식별코드, 생년월일)와 일치하지 않습니다." }); continue; }
          let k = `${st.id}|${row.line}`;
          for (const [ek, ev] of resolved) {
            if (String(ev.student.id) === String(st.id) && sameSitting(ev.row.subject, row.subject)) { k = ek; errors.push({ line: ev.row.line, reason: "동일한 학생, 시험, 영역이 입력 데이터에 중복되어 마지막 행의 값이 적용되었습니다." }); break; }
          }
          resolved.set(k, { row, student: st });
        }
        const studentIds = [...new Set([...resolved.values()].map(v => v.student.id))];
        const existingRows: any[] = [];
        for (const part of chunk(studentIds, 200)) {
          const er = await fetchAll((a, b) => db.from("scores").select("id,student_id,subject").in("student_id", part).order("id").range(a, b));
          if (er.error) return json({ error: "기존 성적을 조회하지 못하였습니다." }, 500);
          existingRows.push(...(er.data ?? []));
        }
        const insertEntries: { rec: any; line: number }[] = [];
        const updateEntries: { rec: any; line: number }[] = [];
        for (const [k, v] of resolved) {
          const rec = { student_id: v.student.id, subject: v.row.subject, score: v.row.n, ...metaColumns(v.row.meta) };
          const found = existingRows.find((x: any) => String(x.student_id) === String(v.student.id) && sameSitting(x.subject, v.row.subject));
          if (found) updateEntries.push({ rec: { id: found.id, ...rec, answers: null }, line: v.row.line });
          else insertEntries.push({ rec, line: v.row.line });
        }
        let saved = 0;
        for (const part of chunk(insertEntries, 200)) {
          const r = await db.from("scores").insert(part.map(p => p.rec));
          if (r.error) part.forEach(p => errors.push({ line: p.line, reason: "저장 중 오류가 발생하였습니다." })); else saved += part.length;
        }
        for (const part of chunk(updateEntries, 200)) {
          const r = await db.from("scores").upsert(part.map(p => p.rec), { onConflict: "id" });
          if (r.error) part.forEach(p => errors.push({ line: p.line, reason: "저장 중 오류가 발생하였습니다." })); else saved += part.length;
        }
        await audit("bulk_scores", `성적 일괄 등록: 저장 ${saved}건, 제외 ${errors.length}건 (신규 성적은 비공개 상태)`);
        errors.sort((a, b) => a.line - b.line);
        return json({ saved, skipped: errors.length, errors: errors.slice(0, 200) });
      }
      case "save_cutoff": {
        const subject = String(body.subject ?? "").trim(), grade = Number(body.grade), min_score = Number(body.min_score);
        if (isEnglish(subject)) return json({ error: "영어 영역은 절대평가이므로 등록할 필요가 없습니다." }, 400);
        const maxScore = maxScoreForSubject(subject);
        if (!subject || subject.length > 160 || !Number.isInteger(grade) || grade < 1 || grade > 8 || !validScore(min_score, maxScore)) return json({ error: `과목, 1~8등급, 0~${maxScore}점 기준 원점수(소수점 첫째 자리까지)를 확인하여 주시기 바랍니다.` }, 400);
        const v = validateWritableSubject(subject, false);
        if (v.error || !v.meta) return json({ error: v.error }, 400);
        const sameGrade = await db.from("grade_cutoffs").select("id,subject").eq("grade", grade);
        if (sameGrade.error) return json({ error: "등급 컷을 저장하지 못하였습니다. migration.sql 및 SCHEMA_NOTES.sql을 먼저 실행하였는지 확인하여 주시기 바랍니다." }, 400);
        const wanted = examKey(subject);
        const found = (sameGrade.data ?? []).find((x: any) => examKey(x.subject) === wanted);
        const editId = body.id ? String(body.id) : "";
        if (editId && found && String(found.id) !== editId) return json({ error: "동일한 시험, 영역, 등급의 기준 원점수가 이미 등록되어 있습니다." }, 409);
        const record = { subject, grade, min_score, ...metaColumns(v.meta) };
        const targetId = editId || (found ? String(found.id) : "");
        const r = targetId
          ? await db.from("grade_cutoffs").update(record).eq("id", targetId).select("id,subject,grade,min_score").single()
          : await db.from("grade_cutoffs").insert(record).select("id,subject,grade,min_score").single();
        if (r.error) return json({ error: "등급 컷을 저장하지 못하였습니다. migration.sql 및 SCHEMA_NOTES.sql을 먼저 실행하였는지 확인하여 주시기 바랍니다." }, 400);
        await audit("save_cutoff", `등급 기준 ${editId ? "수정" : "등록"}: ${subject} / ${grade}등급 / ${min_score}점`);
        return json({ cutoff: r.data });
      }
      case "save_cutoffs": {
        // 한 영역의 1~8등급 기준 원점수를 한 번에 저장한다. 비어 있는 등급은 등록하지 않고, 이미 등록된 등급이 비어 있으면 삭제한다.
        const subject = String(body.subject ?? "").trim();
        if (!subject || subject.length > 160) return json({ error: "시험 정보가 올바르지 않습니다." }, 400);
        if (isEnglish(subject)) return json({ error: "영어 영역은 절대평가이므로 등록할 필요가 없습니다." }, 400);
        const v = validateWritableSubject(subject, false);
        if (v.error || !v.meta) return json({ error: v.error }, 400);
        const maxScore = maxScoreForSubject(subject);
        const wanted = new Map<number, number | null>();
        for (const c of Array.isArray(body.cuts) ? body.cuts : []) {
          const g = Number(c?.grade);
          if (!Number.isInteger(g) || g < 1 || g > 8) return json({ error: "등급은 1~8 사이여야 합니다." }, 400);
          const raw = c?.min_score;
          if (raw === null || raw === undefined || String(raw).trim() === "") { wanted.set(g, null); continue; }
          const n = Number(raw);
          if (!validScore(n, maxScore)) return json({ error: `기준 원점수는 0점 이상 ${maxScore}점 이하의 숫자(소수점 첫째 자리까지)여야 합니다.` }, 400);
          wanted.set(g, n);
        }
        let prev: { g: number; n: number } | null = null;
        for (let g = 1; g <= 8; g++) {
          const n = wanted.get(g);
          if (n === null || n === undefined) continue;
          if (prev && n >= prev.n) return json({ error: `${g}등급 기준 원점수(${n}점)는 ${prev.g}등급 기준 원점수(${prev.n}점)보다 낮아야 합니다.` }, 400);
          prev = { g, n };
        }
        const exRes = await fetchAll((a, b) => db.from("grade_cutoffs").select("id,subject,grade").lte("grade", 8).order("id").range(a, b));
        if (exRes.error) return json({ error: "등급 컷을 저장하지 못하였습니다. migration.sql 및 SCHEMA_NOTES.sql을 먼저 실행하였는지 확인하여 주시기 바랍니다." }, 400);
        const key = examKey(subject);
        const existing = new Map<number, any>();
        const extras: any[] = [];
        // 이전에 응시 일자별로 중복 등록된 기준이 있으면 하나로 통합하고 나머지는 삭제한다.
        for (const x of exRes.data ?? []) {
          if (examKey(x.subject) !== key) continue;
          if (existing.has(Number(x.grade))) extras.push(x.id); else existing.set(Number(x.grade), x);
        }
        const toInsert: any[] = [], toUpdate: any[] = [], toDelete: any[] = [...extras];
        for (const [g, n] of wanted) {
          const ex = existing.get(g);
          if (n === null) { if (ex) toDelete.push(ex.id); continue; }
          const rec = { subject, grade: g, min_score: n, ...metaColumns(v.meta) };
          if (ex) toUpdate.push({ id: ex.id, ...rec }); else toInsert.push(rec);
        }
        if (toDelete.length) { const r = await db.from("grade_cutoffs").delete().in("id", toDelete); if (r.error) return json({ error: "등급 컷을 삭제하지 못하였습니다." }, 400); }
        if (toUpdate.length) { const r = await db.from("grade_cutoffs").upsert(toUpdate, { onConflict: "id" }); if (r.error) return json({ error: "등급 컷을 저장하지 못하였습니다." }, 400); }
        if (toInsert.length) { const r = await db.from("grade_cutoffs").insert(toInsert); if (r.error) return json({ error: "등급 컷을 저장하지 못하였습니다. migration.sql 및 SCHEMA_NOTES.sql을 먼저 실행하였는지 확인하여 주시기 바랍니다." }, 400); }
        await audit("save_cutoffs", `등급 기준 저장: ${subject} / 저장 ${toInsert.length + toUpdate.length}건, 삭제 ${toDelete.length}건`);
        return json({ saved: toInsert.length + toUpdate.length, deleted: toDelete.length });
      }
      case "delete_cutoff": {
        const id = String(body.id ?? ""); if (!id) return json({ error: "등급 컷 ID가 필요합니다." }, 400);
        const existing = await db.from("grade_cutoffs").select("id,subject,grade,min_score").eq("id", id).maybeSingle(); if (existing.error || !existing.data) return json({ error: "등급 컷을 찾지 못하였습니다." }, 404); if (isEnglish(existing.data.subject)) return json({ error: "영어 영역은 절대평가 과목이므로 관리 대상에 해당하지 않습니다." }, 400); const r = await db.from("grade_cutoffs").delete().eq("id", id).select("id").maybeSingle(); if (r.error || !r.data) return json({ error: "등급 컷을 삭제하지 못하였습니다." }, 400);
        await audit("delete_cutoff", `등급 기준 삭제: ${existing.data.subject} / ${existing.data.grade}등급 / ${existing.data.min_score}점`);
        return json({ success: true });
      }
      case "save_answer_key": {
        const m: ExamMeta = { year: String(body.year ?? ""), grade: String(body.grade ?? ""), examType: String(body.examType ?? "").trim(), date: "", dateEnd: "", area: String(body.area ?? "").trim() };
        const variant = String(body.variant ?? "").trim().slice(0, 30);
        const chk = validateWritableSubject(`${m.year}학년도 고등학교 ${m.grade}학년 ${m.examType} / ${m.area}`, false);
        if (chk.error) return json({ error: chk.error }, 400);
        const raw = Array.isArray(body.items) ? body.items : [];
        if (raw.length < 1 || raw.length > 60) return json({ error: "문항 수는 1~60개 사이여야 합니다." }, 400);
        const items: AnswerItem[] = [];
        let total = 0;
        for (let i = 0; i < raw.length; i++) {
          const ans = String(raw[i]?.ans ?? "").replace(/\s+/g, "");
          const pts = Number(raw[i]?.pts);
          if (!/^\d{1,3}(,\d{1,3})*$/.test(ans)) return json({ error: `${i + 1}번 문항의 정답이 올바르지 않습니다. 숫자를 입력하고, 복수 정답은 쉼표로 구분하여 주시기 바랍니다.` }, 400);
          if (!Number.isFinite(pts) || pts <= 0 || pts > 10 || Math.abs(pts * 10 - Math.round(pts * 10)) > 1e-6) return json({ error: `${i + 1}번 문항의 배점은 0.1점 단위로 0보다 크고 10점 이하여야 합니다.` }, 400);
          items.push({ ans, pts }); total += pts;
        }
        const maxScore = maxScoreForSubject(m.area);
        if (total > maxScore + 1e-6) return json({ error: `배점의 합계(${Math.round(total * 10) / 10}점)가 ${maxScore}점을 넘을 수 없습니다.` }, 400);
        const rec = { academic_year: m.year, school_grade: m.grade, exam_type: m.examType, area: m.area, variant, items, updated_at: new Date().toISOString() };
        const up = await db.from("answer_keys").upsert(rec, { onConflict: "academic_year,school_grade,exam_type,area,variant" }).select("id").single();
        if (up.error) return json({ error: "정답을 저장하지 못하였습니다. migration.sql을 실행하였는지 확인하여 주시기 바랍니다." }, 400);
        const rg = await regradeScores(db, m, variant, items);
        await audit("save_answer_key", `정답 저장: ${m.year}학년도 ${m.grade}학년 ${m.examType} / ${m.area}${variant ? ` / ${variant}` : ""} / ${items.length}문항, 배점 합계 ${Math.round(total * 10) / 10}점 / 재채점 ${rg.regraded}건(점수 변경 ${rg.changed}건)`);
        return json({ saved: true, regraded: rg.regraded, changed: rg.changed, total: Math.round(total * 10) / 10 });
      }
      case "delete_answer_key": {
        const id = String(body.id ?? ""); if (!id) return json({ error: "정답 ID가 필요합니다." }, 400);
        const prev = await db.from("answer_keys").select("academic_year,school_grade,exam_type,area,variant").eq("id", id).maybeSingle();
        const r = await db.from("answer_keys").delete().eq("id", id).select("id").maybeSingle();
        if (r.error || !r.data) return json({ error: "정답을 삭제하지 못하였습니다." }, 400);
        await audit("delete_answer_key", prev.data ? `정답 삭제: ${prev.data.academic_year}학년도 ${prev.data.school_grade}학년 ${prev.data.exam_type} / ${prev.data.area}${prev.data.variant ? ` / ${prev.data.variant}` : ""}` : `정답 삭제: ${id}`);
        return json({ success: true });
      }
      case "set_publication": {
        const ids = Array.isArray(body.ids) ? body.ids.map((x: unknown) => String(x)).filter(Boolean) : [];
        if (ids.length < 1 || ids.length > 3000) return json({ error: "대상 성적은 1~3000건이어야 합니다." }, 400);
        const mode = String(body.mode ?? "");
        let when: string | null;
        if (mode === "now") when = new Date().toISOString();
        else if (mode === "hide") when = null;
        else if (mode === "at") {
          const t = new Date(String(body.at ?? ""));
          if (!Number.isFinite(t.getTime())) return json({ error: "예약 일시가 올바르지 않습니다." }, 400);
          if (t.getTime() <= Date.now()) return json({ error: "예약 일시는 현재 시각 이후여야 합니다." }, 400);
          when = t.toISOString();
        } else return json({ error: "공개 방식이 올바르지 않습니다." }, 400);
        for (const part of chunk(ids, 200)) {
          const r = await db.from("scores").update({ published_at: when }).in("id", part);
          if (r.error) return json({ error: "공개 설정을 저장하지 못하였습니다." }, 400);
        }
        const label = mode === "now" ? "즉시 공개" : mode === "hide" ? "비공개 전환" : `예약 공개(${new Date(String(when)).toLocaleString("ko-KR", { timeZone: "Asia/Seoul", hour12: false })})`;
        await audit("set_publication", `성적 공개 설정: ${label} / ${ids.length}건${body.label ? ` / ${String(body.label).slice(0, 120)}` : ""}`);
        return json({ updated: ids.length, published_at: when });
      }
      case "backup_now": {
        try {
          const r = await makeBackup(db);
          lastAutoBackupDay = kstStamp().slice(0, 10);
          await audit("backup_now", `수동 백업 완료: ${r.name}`);
          return json(r);
        } catch (e) { return json({ error: String((e as Error).message || "백업을 만들지 못하였습니다.") }, 500); }
      }
      case "list_backups": {
        const b = await db.storage.getBucket(BACKUP_BUCKET);
        if (b.error || !b.data) return json({ backups: [] });
        const list = await db.storage.from(BACKUP_BUCKET).list("", { limit: 1000, sortBy: { column: "name", order: "desc" } });
        if (list.error) return json({ error: "백업 목록을 불러오지 못하였습니다." }, 500);
        return json({ backups: (list.data ?? []).filter((f: any) => /^\d{4}(-\d{2}){5}\.json$/.test(f.name)).map((f: any) => ({ name: f.name, size: f.metadata?.size ?? 0 })) });
      }
      case "get_backup_url": {
        const name = String(body.name ?? "");
        if (!/^\d{4}(-\d{2}){5}\.json$/.test(name)) return json({ error: "백업 파일명이 올바르지 않습니다." }, 400);
        const r = await db.storage.from(BACKUP_BUCKET).createSignedUrl(name, 600, { download: name });
        if (r.error || !r.data?.signedUrl) return json({ error: "다운로드 주소를 생성하지 못하였습니다." }, 404);
        await audit("download_backup", `백업 내려받기: ${name}`);
        return json({ url: r.data.signedUrl, name });
      }
      default: return json({ error: "지원하지 않는 작업입니다." }, 400);
    }
  } catch (e) {
    console.error("admin-management error", e);
    return json({ error: "요청을 처리하지 못하였습니다." }, 500);
  }
});
