# Export attempt status and preserved artifacts

Both export attempt records retain terminal status `STOPPED`. The first records
a CP932/UTF-8 decoding error before publication. The second records an
`OSError(22, 'Invalid argument')` after a complete plan had been written. The
exporter places its final status print after saving that plan; the retained
record does not provide a traceback locating the final exception precisely.
It is therefore inaccurate to describe the second process as a clean success.

The second plan and all83 published artifacts have independently verified
hashes, correct provenance, a complete native simulation, and the separate
certificate audit. Lean validation uses those exact bytes. The process error
neither supplies a proof nor invalidates the artifacts solely by its status.
Final proof claims depend on the successful Lean receipts.

Both temporary export directories were archived in this milestone. The names
retain `failed-export` because both attempt records stopped with exceptions.
Every archived regular file was compared byte-for-byte by SHA256 with its
source. See data/failed-export-archives.json and data/export-archive-audit.json.
No original export record, source, plan or certificate was overwritten.
