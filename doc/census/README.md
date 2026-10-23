# Census, check and witness files

Provenance of the finite computations cited in the reports. Each file is listed with the
reports (and commissions) that mention it by name. These programs and logs are **not** part of
the Lean build and are not machine-checked; a finite fact is verified only where a Lean theorem
(listed in `axioms.txt`, or in `HPC/Census` for `native_decide`) states it.

`Audit76Long/` holds the batch-76 kernel checks of the extension law at the long stored witnesses
(Lean files; they were a separate Lake library built with `--tstack=4000000`, importing
`HPC.Fold.Target76`). Their content is not reproduced by `HPC/Census`; they are kept here, unbuilt,
and cited by `REPORT-batch76.md`.

| file | cited in |
|---|---|
| `anneal-batch23.py` | REPORT-batch23 |
| `break-batch71.c` | COMMISSION-batch72, REPORT-batch71 |
| `break-batch71.log` | REPORT-batch71 |
| `break-batch72.c` | REPORT-batch72 |
| `break-batch72.log` | REPORT-batch72 |
| `census-batch121-bing56.log` | REPORT-batch121 |
| `census-batch121-bing7-big.log` | REPORT-batch121 |
| `census-batch121-bing7.log` | REPORT-batch121 |
| `census-batch121-k3.log` | REPORT-batch121 |
| `census-batch121-k4a.log` | REPORT-batch121 |
| `census-batch121-k4b.log` | REPORT-batch121 |
| `census-batch121-k5a.log` | REPORT-batch121 |
| `census-batch121-k5b.log` | REPORT-batch121 |
| `census-batch121.c` | REPORT-batch121 |
| `census-batch16.py` | REPORT-batch16 |
| `census-batch17.py` | REPORT-batch17 |
| `census-batch18.py` | REPORT-batch18 |
| `census-batch19.py` | REPORT-batch19, REPORT-batch20 |
| `census-batch20.py` | REPORT-batch20 |
| `census-batch22.py` | REPORT-batch22 |
| `census-batch23.py` | REPORT-batch23 |
| `census-batch24.py` | REPORT-batch24, REPORT-batch25, REPORT-batch54 |
| `census-batch25.py` | REPORT-batch25 |
| `census-batch26.py` | REPORT-batch26, REPORT-batch74 |
| `census-batch27.py` | REPORT-batch27 |
| `census-batch28.c` | REPORT-batch28 |
| `census-batch28.log` | REPORT-batch28 |
| `census-batch29.c` | REPORT-batch29 |
| `census-batch29.log` | REPORT-batch29 |
| `census-batch30.c` | REPORT-batch30 |
| `census-batch30.log` | REPORT-batch30 |
| `census-batch31.c` | REPORT-batch31 |
| `census-batch31.log` | REPORT-batch31 |
| `census-batch32.c` | REPORT-batch32 |
| `census-batch32.log` | REPORT-batch32 |
| `census-batch33.c` | REPORT-batch33 |
| `census-batch33.log` | REPORT-batch33 |
| `census-batch34.c` | REPORT-batch34 |
| `census-batch34.log` | REPORT-batch34 |
| `census-batch35.c` | REPORT-batch35 |
| `census-batch35.log` | REPORT-batch35 |
| `census-batch36.c` | REPORT-batch36 |
| `census-batch36.log` | REPORT-batch36 |
| `census-batch37.log` | REPORT-batch37 |
| `census-batch37.py` | REPORT-batch37 |
| `census-batch38.log` | REPORT-batch38 |
| `census-batch38.py` | REPORT-batch38 |
| `census-batch39.c` | REPORT-batch39 |
| `census-batch39.log` | REPORT-batch39 |
| `census-batch39b.c` | REPORT-batch39 |
| `census-batch40.c` | REPORT-batch40, REPORT-batch41 |
| `census-batch40.log` | REPORT-batch40 |
| `census-batch40b.c` | REPORT-batch40 |
| `census-batch40b.log` | REPORT-batch40 |
| `census-batch41.c` | REPORT-batch41 |
| `census-batch41.log` | REPORT-batch41 |
| `census-batch41b.c` | REPORT-batch41 |
| `census-batch41b.log` | REPORT-batch41 |
| `census-batch41c.c` | REPORT-batch41 |
| `census-batch41c.log` | REPORT-batch41 |
| `census-batch41d.c` | (no report cites this file by name) |
| `census-batch41e.c` | (no report cites this file by name) |
| `census-batch41f.c` | REPORT-batch41 |
| `census-batch41f.log` | (no report cites this file by name) |
| `census-batch41g.c` | (no report cites this file by name) |
| `census-batch41h.c` | REPORT-batch41 |
| `census-batch41h.log` | REPORT-batch41 |
| `census-batch42.c` | COMMISSION-batch43, REPORT-batch42 |
| `census-batch42.log` | (no report cites this file by name) |
| `census-batch42b.c` | REPORT-batch42 |
| `census-batch42b.log` | (no report cites this file by name) |
| `census-batch42c.c` | COMMISSION-batch43, REPORT-batch42 |
| `census-batch42c.log` | (no report cites this file by name) |
| `census-batch42d.c` | REPORT-batch42 |
| `census-batch42d.log` | (no report cites this file by name) |
| `census-batch42e.c` | REPORT-batch42 |
| `census-batch42f.c` | REPORT-batch42 |
| `census-batch42f.log` | (no report cites this file by name) |
| `census-batch42g.c` | COMMISSION-batch43, REPORT-batch42 |
| `census-batch42g.log` | (no report cites this file by name) |
| `census-batch42h.c` | REPORT-batch42 |
| `census-batch42h.log` | COMMISSION-batch43 |
| `census-batch42i.c` | REPORT-batch42 |
| `census-batch42i.log` | (no report cites this file by name) |
| `census-batch42j.c` | REPORT-batch42 |
| `census-batch42j.log` | (no report cites this file by name) |
| `census-batch42k.c` | REPORT-batch42, REPORT-batch43 |
| `census-batch42k.log` | (no report cites this file by name) |
| `census-batch43.c` | REPORT-batch43, REPORT-batch44, REPORT-batch45 |
| `census-batch43.log` | REPORT-batch43 |
| `census-batch44.c` | REPORT-batch44 |
| `census-batch44.log` | REPORT-batch44 |
| `census-batch44b.c` | REPORT-batch44 |
| `census-batch44b.log` | REPORT-batch44 |
| `census-batch45.c` | REPORT-batch45 |
| `census-batch45.log` | REPORT-batch45 |
| `census-batch45b.c` | REPORT-batch45 |
| `census-batch45b.log` | REPORT-batch45 |
| `census-batch46.c` | REPORT-batch46 |
| `census-batch46.log` | REPORT-batch46 |
| `census-batch46b.c` | REPORT-batch46 |
| `census-batch46b.log` | REPORT-batch46 |
| `census-batch46d-all.log` | REPORT-batch46 |
| `census-batch46d-rand.log` | REPORT-batch46 |
| `census-batch46d.c` | REPORT-batch46 |
| `census-batch46d.log` | REPORT-batch46 |
| `census-batch46e.c` | REPORT-batch46 |
| `census-batch46e.log` | REPORT-batch46 |
| `census-batch46f.c` | REPORT-batch46 |
| `census-batch46f.log` | REPORT-batch46 |
| `census-batch47.c` | REPORT-batch47 |
| `census-batch47.log` | REPORT-batch47 |
| `census-batch47b.c` | REPORT-batch47 |
| `census-batch47b.log` | REPORT-batch47 |
| `census-batch47c.c` | COMMISSION-batch48, COMMISSION-batch59, REPORT-batch47, REPORT-batch48 |
| `census-batch47c.log` | REPORT-batch47 |
| `census-batch47d.c` | REPORT-batch47 |
| `census-batch47d.log` | REPORT-batch47 |
| `census-batch48.c` | REPORT-batch48 |
| `census-batch48.log` | REPORT-batch48 |
| `census-batch48b.c` | REPORT-batch48 |
| `census-batch48b.log` | REPORT-batch48 |
| `census-batch49.c` | REPORT-batch49 |
| `census-batch49.log` | REPORT-batch49 |
| `census-batch49b.c` | REPORT-batch49 |
| `census-batch49b.log` | REPORT-batch49 |
| `census-batch49c.c` | REPORT-batch49 |
| `census-batch49c.log` | REPORT-batch49 |
| `census-batch49d.log` | REPORT-batch49 |
| `census-batch50-audit.txt` | REPORT-batch50 |
| `census-batch50.c` | REPORT-batch50 |
| `census-batch50.log` | REPORT-batch50 |
| `census-batch51-arms.log` | REPORT-batch51 |
| `census-batch51-audit.txt` | REPORT-batch51 |
| `census-batch51.c` | REPORT-batch51, REPORT-batch52 |
| `census-batch51.log` | REPORT-batch51 |
| `census-batch51.py` | REPORT-batch51 |
| `census-batch52-audit.txt` | (no report cites this file by name) |
| `census-batch52.c` | REPORT-batch52, REPORT-batch53 |
| `census-batch52.log` | REPORT-batch52 |
| `census-batch53-sample.txt` | REPORT-batch53 |
| `census-batch53.c` | REPORT-batch53, REPORT-batch54 |
| `census-batch53.log` | REPORT-batch53 |
| `census-batch54-sample.txt` | REPORT-batch54 |
| `census-batch54.c` | REPORT-batch54 |
| `census-batch54.log` | REPORT-batch54 |
| `census-batch55-sample.txt` | REPORT-batch55 |
| `census-batch55-sigma.txt` | REPORT-batch55 |
| `census-batch55.c` | REPORT-batch55 |
| `census-batch55.log` | REPORT-batch55 |
| `census-batch56.c` | REPORT-batch56 |
| `census-batch56.log` | REPORT-batch56 |
| `census-batch57.c` | REPORT-batch57 |
| `census-batch57.log` | REPORT-batch57 |
| `census-batch58.c` | REPORT-batch58, REPORT-batch59 |
| `census-batch58.log` | REPORT-batch58 |
| `census-batch59.c` | REPORT-batch59 |
| `census-batch59.log` | REPORT-batch59 |
| `census-batch60.c` | REPORT-batch60 |
| `census-batch60.log` | REPORT-batch60 |
| `census-batch61.c` | REPORT-batch61 |
| `census-batch61.log` | REPORT-batch61 |
| `census-batch62.c` | REPORT-batch62 |
| `census-batch62.log` | REPORT-batch62 |
| `census-batch63.c` | REPORT-batch63 |
| `census-batch63.log` | REPORT-batch63 |
| `census-batch64.c` | REPORT-batch64 |
| `census-batch64.log` | REPORT-batch64 |
| `census-batch65.c` | REPORT-batch65 |
| `census-batch65.log` | REPORT-batch65 |
| `census-batch68.c` | REPORT-batch68, REPORT-batch69 |
| `census-batch68.log` | REPORT-batch68 |
| `census-batch69.c` | REPORT-batch69 |
| `census-batch69.log` | REPORT-batch69 |
| `census-batch70.c` | REPORT-batch70 |
| `census-batch70.log` | REPORT-batch70 |
| `census-batch71-rows.csv` | REPORT-batch71 |
| `census-batch71.c` | REPORT-batch71, REPORT-batch72 |
| `census-batch71.log` | REPORT-batch71 |
| `census-batch72.c` | REPORT-batch72 |
| `census-batch72.log` | REPORT-batch72 |
| `census-batch74-span10.log` | (no report cites this file by name) |
| `census-batch74-span11.log` | (no report cites this file by name) |
| `census-batch74-span12.log` | REPORT-batch74 |
| `census-batch74-span9.log` | REPORT-batch74 |
| `census-batch74.c` | REPORT-batch74 |
| `census-batch75-span10.log` | REPORT-batch76 |
| `census-batch75-span11.log` | (no report cites this file by name) |
| `census-batch75-span12.log` | (no report cites this file by name) |
| `census-batch75-span13.log` | (no report cites this file by name) |
| `census-batch75-span14.log` | REPORT-batch75 |
| `census-batch75-span8.log` | REPORT-batch75 |
| `census-batch75-span9.log` | (no report cites this file by name) |
| `census-batch75.c` | REPORT-batch75 |
| `census-batch76-span10.log` | (no report cites this file by name) |
| `census-batch76-span11.log` | (no report cites this file by name) |
| `census-batch76-span12.log` | (no report cites this file by name) |
| `census-batch76-span13.log` | (no report cites this file by name) |
| `census-batch76-span14.log` | REPORT-batch76 |
| `census-batch76-span8.log` | REPORT-batch76 |
| `census-batch76-span9.log` | (no report cites this file by name) |
| `census-batch76.c` | REPORT-batch76 |
| `census-batch86-bing.c` | REPORT-batch86 |
| `census-batch86-bing.log` | (no report cites this file by name) |
| `census-batch86-exhaustive.c` | REPORT-batch86 |
| `census-batch86-exhaustive.log` | (no report cites this file by name) |
| `census-batch87-bing.log` | REPORT-batch87 |
| `census-batch87-common.h` | REPORT-batch87 |
| `census-batch87-k4.log` | REPORT-batch87 |
| `census-batch87-k5.log` | REPORT-batch87 |
| `census-batch87-model.c` | REPORT-batch87 |
| `check68.log` | COMMISSION-batch70, PROBE-batch68, REPORT-batch68, REPORT-batch69 |
| `check68.py` | PROBE-batch68, REPORT-batch68 |
| `check70.log` | REPORT-batch70 |
| `check70.py` | REPORT-batch70 |
| `check71.log` | REPORT-batch71 |
| `check71.py` | REPORT-batch71 |
| `check72.log` | REPORT-batch72 |
| `check72.py` | REPORT-batch72 |
| `check74-span12.log` | REPORT-batch74 |
| `check74.log` | REPORT-batch74 |
| `check74.py` | REPORT-batch74 |
| `check75-span10-k4.log` | (no report cites this file by name) |
| `check75-span10-k5.log` | REPORT-batch75 |
| `check75-span11-k4.log` | (no report cites this file by name) |
| `check75-span11-k5.log` | (no report cites this file by name) |
| `check75-span12-k4.log` | (no report cites this file by name) |
| `check75-span12-k5.log` | REPORT-batch75 |
| `check75-span12-k6.log` | REPORT-batch75 |
| `check75-span13-k5.log` | (no report cites this file by name) |
| `check75-span13-k6.log` | REPORT-batch75 |
| `check75-span14-k4.log` | (no report cites this file by name) |
| `check75-span14-k5.log` | (no report cites this file by name) |
| `check75-span14-k6.log` | REPORT-batch75 |
| `check75-span9-k4.log` | (no report cites this file by name) |
| `check75.py` | REPORT-batch75, REPORT-batch76 |
| `check76-least.log` | REPORT-batch76 |
| `check76-q2.log` | REPORT-batch76 |
| `engine-batch55-p6m3.log` | REPORT-batch55 |
| `engine-batch55.c` | REPORT-batch55 |
| `engine-batch55.log` | REPORT-batch55 |
| `explore-auto.py` | (no report cites this file by name) |
| `explore-auto2.py` | (no report cites this file by name) |
| `explore-auto3.py` | (no report cites this file by name) |
| `explore-auto4.py` | (no report cites this file by name) |
| `ext76.py` | REPORT-batch76 |
| `gap-batch52.c` | REPORT-batch52 |
| `gap-batch52.log` | (no report cites this file by name) |
| `gap-batch54.c` | REPORT-batch54 |
| `gap-batch54.log` | REPORT-batch54 |
| `gen-audit50.py` | REPORT-batch50 |
| `gen-audit51.py` | REPORT-batch51 |
| `gen-audit52.py` | REPORT-batch52 |
| `gen-audit55.py` | REPORT-batch55 |
| `gen-audit58.py` | REPORT-batch58 |
| `gen-audit76.py` | REPORT-batch76 |
| `greedy-batch39.py` | (no report cites this file by name) |
| `greedy77.c` | REPORT-batch77 |
| `invariant-batch39.py` | (no report cites this file by name) |
| `min-batch71.c` | REPORT-batch71 |
| `min-batch71.log` | REPORT-batch71 |
| `min-batch72.c` | REPORT-batch72 |
| `min-batch72.log` | REPORT-batch72 |
| `mk59.py` | REPORT-batch59 |
| `parametric-batch74.log` | REPORT-batch74 |
| `parametric-batch74.py` | REPORT-batch74 |
| `probe59.c` | REPORT-batch59 |
| `probe59.log` | REPORT-batch59 |
| `probe59b.c` | REPORT-batch59 |
| `probe59b.log` | REPORT-batch59 |
| `probe59c.c` | REPORT-batch59 |
| `probe59c.log` | REPORT-batch59 |
| `probe60.c` | REPORT-batch60 |
| `probe60.log` | (no report cites this file by name) |
| `probe60b.c` | REPORT-batch60 |
| `probe60b.log` | REPORT-batch60 |
| `probe61.c` | REPORT-batch61 |
| `probe61.log` | REPORT-batch61 |
| `probe63.c` | REPORT-batch63, REPORT-batch64 |
| `probe63.log` | REPORT-batch63 |
| `probe63b.log` | REPORT-batch63 |
| `probe64.c` | REPORT-batch64 |
| `probe64.log` | REPORT-batch64 |
| `probe64b.log` | REPORT-batch64 |
| `probe64c.log` | REPORT-batch64 |
| `probe65.c` | REPORT-batch65 |
| `probe65.log` | REPORT-batch65 |
| `probe65b.c` | PROBE-batch68, REPORT-batch65, REPORT-batch68 |
| `probe65b.log` | REPORT-batch65 |
| `probe68.c` | PROBE-batch68, REPORT-batch68 |
| `probe68.log` | PROBE-batch68, REPORT-batch68 |
| `probe68b.log` | PROBE-batch68, REPORT-batch68 |
| `probe68c.log` | PROBE-batch68, REPORT-batch68 |
| `recon-batch122-bing-5-frames.log` | REPORT-batch122 |
| `recon-batch122-bing-6-frames.log` | REPORT-batch122 |
| `recon-batch122-bing-7-frames.log` | REPORT-batch122 |
| `recon-batch122-bing-7.log` | REPORT-batch122 |
| `recon-batch122-bing-8.log` | REPORT-batch122 |
| `recon-batch122-bing.py` | REPORT-batch122 |
| `recon-batch122-enum-3-3-10.log` | REPORT-batch122 |
| `recon-batch122-enum-4-4-11.log` | REPORT-batch122 |
| `recon-batch122-enum-5-11-13.log` | REPORT-batch122 |
| `recon-batch122-q1-bing6.log` | REPORT-batch122 |
| `recon-batch122-q1-k5-list11.log` | REPORT-batch122 |
| `recon-batch122-q1-k5.log` | REPORT-batch122 |
| `recon-batch122-q1-k6.log` | REPORT-batch122 |
| `recon-batch122-q1-k6b.log` | REPORT-batch122 |
| `recon-batch122-q1.py` | REPORT-batch122 |
| `recon-batch122-special-5-11-12.log` | REPORT-batch122 |
| `recon-batch122-special-5-13-13.log` | REPORT-batch122 |
| `recon-batch123-nocontain.log` | REPORT-batch123 |
| `recon-batch123-only.log` | REPORT-batch123 |
| `recon-batch123-only.py` | REPORT-batch123 |
| `recon-batch123-pair.log` | REPORT-batch123 |
| `recon-batch124-only.log` | REPORT-batch124 |
| `recon-batch124-pair.cpp` | REPORT-batch124 |
| `recon-batch124-pair.log` | REPORT-batch124 |
| `recon-batch124-thm4.log` | REPORT-batch124 |
| `seam-batch121.log` | REPORT-batch121 |
| `seam-batch121.py` | REPORT-batch121 |
| `seam-batch55.log` | REPORT-batch55 |
| `seam-batch55.py` | COMMISSION-batch56, REPORT-batch55 |
| `seam-batch56.log` | REPORT-batch56 |
| `seam-batch56.py` | COMMISSION-batch57, REPORT-batch56, REPORT-batch57 |
| `seam-batch57.log` | REPORT-batch57 |
| `seam-batch57.py` | REPORT-batch57 |
| `search-batch23.py` | REPORT-batch23 |
| `search-batch24.py` | REPORT-batch24 |
| `search-batch25.py` | REPORT-batch25 |
| `search-batch50.c` | REPORT-batch50 |
| `search-batch50.log` | REPORT-batch50 |
| `search-batch52.c` | REPORT-batch52 |
| `search-batch53.c` | REPORT-batch53 |
| `search-batch53.log` | REPORT-batch53 |
| `search-batch54-hits.txt` | REPORT-batch54 |
| `search-batch54.c` | REPORT-batch54 |
| `search-batch54.log` | REPORT-batch54 |
| `seeds-batch71.txt` | REPORT-batch71 |
| `seeds-batch72.txt` | REPORT-batch72 |
| `witness-batch70.txt` | REPORT-batch70 |
| `witness-batch71-bothnine.txt` | (no report cites this file by name) |
| `witness-batch71-min.txt` | REPORT-batch71, REPORT-batch76 |
| `witness-batch71.txt` | REPORT-batch71 |
| `witness-batch72-c0.txt` | REPORT-batch72 |
| `witness-batch72-c1.txt` | (no report cites this file by name) |
| `witness-batch72-c2.txt` | (no report cites this file by name) |
| `witness-batch72-min.txt` | REPORT-batch72, REPORT-batch76 |
| `witness-batch74-span11.txt` | REPORT-batch74, REPORT-batch76 |
| `witness-batch74-span12.txt` | REPORT-batch74, REPORT-batch76 |
| `witness-batch75-span10-k4.txt` | REPORT-batch76 |
| `witness-batch75-span10-k5.txt` | REPORT-batch75, REPORT-batch76 |
| `witness-batch75-span11-k4.txt` | REPORT-batch76 |
| `witness-batch75-span11-k5.txt` | REPORT-batch76 |
| `witness-batch75-span12-k4.txt` | REPORT-batch76 |
| `witness-batch75-span12-k5.txt` | REPORT-batch76 |
| `witness-batch75-span12-k6.txt` | REPORT-batch75, REPORT-batch76 |
| `witness-batch75-span13-k4.txt` | (no report cites this file by name) |
| `witness-batch75-span13-k5.txt` | (no report cites this file by name) |
| `witness-batch75-span13-k6.txt` | (no report cites this file by name) |
| `witness-batch75-span14-k4.txt` | (no report cites this file by name) |
| `witness-batch75-span14-k5.txt` | (no report cites this file by name) |
| `witness-batch75-span14-k6.txt` | (no report cites this file by name) |
| `witness-batch75-span9-k4.txt` | REPORT-batch76 |
| `witness-batch76-q2-span10-1.txt` | REPORT-batch76 |
| `witness-batch76-q2-span10-2.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span10-3.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span10-4.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span10-5.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span10-6.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span11-1.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span11-2.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span11-3.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span11-4.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span11-5.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span11-6.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span12-1.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span12-2.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span12-3.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span12-4.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span12-5.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span12-6.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span13-1.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span13-2.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span13-3.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span13-4.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span13-5.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span13-6.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span14-1.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span14-2.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span14-3.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span14-4.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span14-5.txt` | (no report cites this file by name) |
| `witness-batch76-q2-span14-6.txt` | (no report cites this file by name) |
| `zig77.py` | REPORT-batch77 |
| `Audit76Long` | COMMISSION-batch103, REPORT-batch76 |
