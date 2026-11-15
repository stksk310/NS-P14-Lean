#!/usr/bin/env python3
"""Build the canonical proof and a documented pagination reference; no old writes."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "proof_sharp_v6"
BUILD = OUT / "build"


def between(text, start, end=None):
    a = text.index(start)
    b = text.index(end, a + len(start)) if end else len(text)
    return text[a:b].strip()


def main():
    BUILD.mkdir(exist_ok=True)
    chapter_names = ["01_COMMON_JA.md", "02_ORDINARY_JA.md", "03_ENDPOINT_JA.md",
                     "04_WIDTH_JA.md", "04A_ANTIPODAL_JA.md", "05_N4_JA.md",
                     "06_SYNTHESIS_JA.md"]
    chunks = ["# NS-P14：簡約された全域証明 V06\n\n"
              "読解基準：work commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。\n"
              "本稿は公刊入力を引用する紙上証明である。既存Leanとの対応、\n"
              "新しい紙上補題、形式化の未到達範囲は別冊の変更台帳に記録する。\n"
              "全体の論証に必要な付録はなく、今回固有の補題は以下に展開する。"]
    for name in chapter_names:
        chunks.append((OUT / "chapters" / name).read_text())
    canonical = OUT / "NS_P14_SHARP_PROOF_JA.md"
    canonical.write_text("\n\n".join(chunks) + "\n")

    old = (ROOT / "proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md").read_text()
    so = (ROOT / "auditability_search/ORDINARY_PAPER_REDUCTION_JA.md").read_text()
    n4 = (ROOT / "n4_further_reduction/N4_PAPER_REDUCTION_JA.md").read_text()
    core = (ROOT / "auditability_search/CORE_READABILITY_AUDIT.md").read_text()
    later = (ROOT / "auditability_search/LATER_READABILITY_AUDIT.md").read_text()
    reference_parts = [
        "# 現行選択経路の組版参照本\n\n"
        "これはページ数比較のための機械的な参照本であり、新しいcanonical本文ではない。\n"
        "V02の必要章、既に採用済みのordinary/N4置換証明、監査時の接続展開を収録した。\n"
        "旧節番号と文脈の歴史的文言は残る。旧§15と196組証書は含めない。\n"
        "節の接合・重複の整理を伴う実際の現行一本化原稿にはページ数の幅を見込む。",
        between(old, "## 1 主張", "## 11 固定cutoff"),
        "## 採用済み小ordinary置換\n\n" + between(so, "## 1 二次層", "## 4 全ordinary"),
        "## 大rankの既存経路（r≥9に限定）\n\n" + between(old, "### 11.1", "### 11.2"),
        "### r=9の基点\n\n"
        "\\(a=45,D=23,T_9=269/72\\) とし、既存の(S9)は\n"
        "\\[G_9(10,45;23)=8\\cdot54(T_9-\\mathcal H_{23}).\\]\n"
        "\\(\\mathcal H_{23}=444316699/118982864\\)、\n"
        "\\(747/200-\\mathcal H_{23}=2107451/2974571600>0\\)、\n"
        "\\(T_9-747/200=1/900>0\\) なので基点は正である。",
        between(old, "### 11.3", "## 12 共通端点"),
        between(old, "## 12 共通端点", "## 14 四生成元"),
        between(old, "## 14 四生成元", "### 14.5"),
        "## 採用済みN4第一行置換\n\n" + between(n4, "## 2 三つの端点関係", "最後の \\(d=1,u=4"),
        between(old, "### 14.6", "## 15 小ordinary"),
        "## 監査の接続展開（既存数学の一部）\n\n" + between(core, "## §2・§5", "## 点検の方法"),
        between(later, "## 1. 最優先", "## 4. 高優先"),
        between(later, "## 5. 中優先", "## 6. 依存版"),
        (OUT / "chapters/06_SYNTHESIS_JA.md").read_text(),
    ]
    reference = OUT / "CURRENT_ROUTE_PAGINATION_REFERENCE_JA.md"
    reference_text = "\n\n".join(reference_parts) + "\n"
    # Old audit prose uses raw mathematical Unicode and Japanese in inline code.
    # Preserve its notation using TeX math; inline-code styling is not mathematical content.
    reference_text = re.sub(r"`([^`\n]+)`", lambda m: m.group(1), reference_text)
    reference_text = (reference_text.replace("𝒱", r"\(\mathcal V\)")
                      .replace("𝒟", r"\(\mathscr D\)").replace("↦", r"\(\mapsto\)"))
    # Break long old displayed lists at their original comma/quad separators.
    # No font-size or margin reduction is used in either version.
    def wrap_old_display(match):
        body = match.group(1)
        if len(body) < 90 or r"\begin" in body or r"\quad" not in body:
            return match.group(0)
        tag = re.search(r"\\tag\{[^}]*\}", body)
        suffix = tag.group(0) if tag else ""
        if tag:
            body = body.replace(suffix, "")
        pieces = re.split(r",\s*\\q(?:q)?uad\s*", body.strip())
        rows, row = [], ""
        for piece in pieces:
            if row and len(row)+len(piece) > 70:
                rows.append(row)
                row = piece
            else:
                row += (r",\quad " if row else "") + piece
        if row:
            rows.append(row)
        body = ",\\\\\n".join(rows)
        return "\\[\n\\begin{gathered}\n" + body + "\n\\end{gathered}" + suffix + "\n\\]"
    reference_text = re.sub(r"\\\[(.*?)\\\]", wrap_old_display, reference_text, flags=re.S)
    reference_text = reference_text.replace(
        r"\((F_2^{\min},F_3^{\min},F_4^{\min},F_5^{\min})\)", "targetの第2–5行最小値")
    reference_text = reference_text.replace(
        r"\((\theta_0,\theta_1,\theta_2,\theta_3,\theta_6)\)", "閾値列（0,1,2,3,6の順）")
    reference_text = reference_text.replace(
        " &=\\delta\\binom{r-1}{j-1}\n +\\frac12\\sum_{u=2}^j\n ",
        " &=\\delta\\binom{r-1}{j-1}\\\\\n &\\quad+\\frac12\\sum_{u=2}^j\n ")
    reference.write_text(reference_text)

    header = BUILD / "pagination_header.tex"
    header.write_text(r"""\XeTeXlinebreaklocale "ja"
\XeTeXlinebreakskip=0pt plus 0.15em
\setlength{\emergencystretch}{3em}
\AtBeginDocument{\hypersetup{breaklinks=true}}
""")
    env = os.environ.copy()
    env["XDG_CACHE_HOME"] = "/tmp/ns-p14-font-cache"
    outputs = []
    for stem, source in [("NS_P14_SHARP_PROOF_JA", canonical),
                         ("CURRENT_ROUTE_PAGINATION_REFERENCE_JA", reference)]:
        tex = BUILD / (stem + ".tex")
        pandoc = ["pandoc", str(source), "--standalone", "--from=markdown+tex_math_single_backslash",
                  "--to=latex", "--variable=documentclass:article", "--variable=fontsize:11pt",
                  "--variable=papersize:a4", "--variable=geometry:margin=25mm",
                  "--variable=mainfont:Noto Serif CJK JP", "--variable=monofont:Noto Sans Mono CJK JP",
                  "--include-in-header=" + str(header), "--output=" + str(tex)]
        subprocess.run(pandoc, cwd=ROOT, env=env, check=True)
        for run in [1, 2]:
            result = subprocess.run(["xelatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
                                    cwd=BUILD, env=env, capture_output=True, text=True)
            (BUILD / f"{stem}.pass{run}.stdout.log").write_text(result.stdout + result.stderr)
            if result.returncode:
                print(result.stdout[-6000:])
                raise SystemExit(result.returncode)
        pdf = BUILD / (stem + ".pdf")
        info = subprocess.run(["pdfinfo", str(pdf)], capture_output=True, text=True, check=True).stdout
        pages = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))
        log = (BUILD / (stem + ".log")).read_text(errors="replace")
        outputs.append({"source": str(source.relative_to(ROOT)), "pdf": str(pdf.relative_to(ROOT)),
                        "pages": pages, "source_characters": len(source.read_text()),
                        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                        "tex": str(tex.relative_to(ROOT)),
                        "tex_sha256": hashlib.sha256(tex.read_bytes()).hexdigest(),
                        "sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
                        "missing_character_warnings": log.count("Missing character:"),
                        "overfull_boxes": log.count("Overfull "),
                        "measured_reference_is_complete_current_manuscript": False
                        if stem.startswith("CURRENT") else None})
        print(stem, pages, "pages; missing glyph warnings", outputs[-1]["missing_character_warnings"])
    (OUT / "PAGINATION.json").write_text(json.dumps({
        "format": {"engine": "XeLaTeX", "paper": "A4", "font_size_pt": 11,
                   "columns": 1, "margin_mm": 25, "font": "Noto Serif CJK JP",
                   "published_theorems": "cited, not reproved", "required_appendix_pages": 0},
        "outputs": outputs,
        "revision": "V06",
        "previous_revision": {
            "revision": "V05",
            "source": "proof_sharp_v5/NS_P14_SHARP_PROOF_JA.md",
            "pdf": "proof_sharp_v5/build/NS_P14_SHARP_PROOF_JA.pdf",
            "pages": json.loads((ROOT / "proof_sharp_v5/PAGINATION.json").read_text())["outputs"][0]["pages"],
            "source_characters": len((ROOT / "proof_sharp_v5/NS_P14_SHARP_PROOF_JA.md").read_text()),
            "source_sha256": hashlib.sha256((ROOT / "proof_sharp_v5/NS_P14_SHARP_PROOF_JA.md").read_bytes()).hexdigest(),
            "sha256": hashlib.sha256((ROOT / "proof_sharp_v5/build/NS_P14_SHARP_PROOF_JA.pdf").read_bytes()).hexdigest(),
        },
        "limitation": "The current-route reference is assembled source material, not a new verified canonical manuscript. Its page count is a reference measurement; a clean current-route estimate must retain uncertainty."
    }, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
