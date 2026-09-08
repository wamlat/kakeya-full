# Revised Kakeya manuscripts

- `kakeya_paper_i.pdf`: standalone six-dimensional 33/8 argument.
- `kakeya_combined.pdf`: full manuscript including the real-cap iteration (builds on paper 1).

Editable Markdown (`.md`) and generated standalone LaTeX (`.tex`) are included for both manuscripts. Original Markdown and unified diffs are in `originals/` and `diffs/`.

## Build

Install Python 3, Pandoc and a TeX distribution with XeLaTeX, Latin Modern fonts, unicode-math, microtype, etoolbox, titlesec and needspace.

Run from this folder:

```sh
python3 build_papers.py kakeya_paper_i
python3 build_papers.py kakeya_combined
```

The script runs Pandoc and three XeLaTeX passes. It retains the numbered equations and formats the wide iteration table. Each generated `.tex` also compiles independently with XeLaTeX; run it twice for contents and links.

`checks/check_preservation.py` reproduces the display, numbering and approximate prose-count comparison. It uses only Python's standard library. These checks establish editorial preservation, not validity of the underlying proof.
