"""Build either manuscript using Pandoc and XeLaTeX.

Run: python3 build_papers.py kakeya_combined
     python3 build_papers.py kakeya_paper_i
The generated kakeya_combined.tex is also standalone:
    xelatex kakeya_combined.tex  (run twice)
"""
from pathlib import Path
import sys
import re
import subprocess

HERE = Path(__file__).resolve().parent
STEM = HERE / (sys.argv[1] if len(sys.argv) > 1 else 'kakeya_combined')
if STEM.name not in {'kakeya_combined', 'kakeya_paper_i'}:
    raise SystemExit('Choose kakeya_combined or kakeya_paper_i')

PROFILE_TABLE = r"""\begin{center}
\small
\setlength{\tabcolsep}{5pt}
\begin{tabular}{@{}rrrr@{}}
\toprule
Depth & Slope $a_j$ & $d_j(5)$: dimension 6 & $d_j(7)$: dimension 8 \\
\midrule
$0$ & $1/2$ & $4$ & $5$ \\
$1$ & $9/16$ & $33/8$ & $21/4$ \\
$2$ & $593/1024$ & $2129/512$ & $1361/256$ \\
$3$ & $2448801/4194304$ & $8740257/2097152$ & $5594529/1048576$ \\
Limit & $2-\sqrt2$ & $7-2\sqrt2$ & $11-4\sqrt2$ \\
\bottomrule
\end{tabular}
\end{center}"""

subprocess.run([
    'pandoc', str(STEM.with_suffix('.md')),
    '--from=markdown+tex_math_single_backslash', '--standalone', '--to=latex',
    '-V', 'mainfont=Latin Modern Roman', '-V', 'mathfont=Latin Modern Math',
    '-V', 'papersize=a4', '-V', 'colorlinks=true',
    '-V', 'linkcolor=black', '-V', 'urlcolor=blue',
    f'--include-in-header={HERE / "paper_style.tex"}',
    '-o', str(STEM.with_suffix('.tex')),
], check=True)

text = STEM.with_suffix('.tex').read_text()
tables = list(re.finditer(r'\\begin\{longtable\}.*?\\end\{longtable\}', text, re.S))
profile = [m for m in tables if '2448801' in m.group()]
if STEM.name == 'kakeya_combined':
    assert len(profile) == 1
    m = profile[0]
    text = text[:m.start()] + PROFILE_TABLE + text[m.end():]

# Named equation anchors make future edits and cross-references easier while
# preserving the manuscript's displayed numbering.
text = re.sub(r'\\tag\{([0-9A-Z]+(?:\.[0-9]+)?)\}',
              lambda m: m.group() + r'\label{eq:' + m[1] + '}', text)
STEM.with_suffix('.tex').write_text(text)

for _ in range(3):
    result = subprocess.run([
        'xelatex', '-interaction=nonstopmode', '-halt-on-error',
        f'-output-directory={HERE}', str(STEM.with_suffix('.tex')),
    ], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, cwd=HERE)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)

warnings = [line for line in STEM.with_suffix('.log').read_text().splitlines()
            if any(s in line for s in ('Warning', 'Overfull', 'Undefined', 'Missing character'))]
print(STEM.with_suffix('.pdf'))
print('Compiler warnings:', warnings)
