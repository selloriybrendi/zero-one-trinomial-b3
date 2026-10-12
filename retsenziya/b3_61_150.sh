#!/bin/bash
# b=3, 61 <= k <= 150 (k≢0 mod 3): to'liq sertifikat (GCD_TEKSHIR=1, nuqtaviy), 9 parallel
cd "$(dirname "$0")/.."
LOG=retsenziya/b3_61_150.log; : > $LOG
run(){ GCD_TEKSHIR=1 timeout 3600 ~/arsenal-venv/bin/python simvolik_isbot_flint.py $1 $2 4000 2>/dev/null | tail -1 >> $LOG; }
export -f run; export LOG
xargs -P 9 -L 1 bash -c 'run $0 $1' < retsenziya/b3_61_150.txt
echo "B3-TUGADI" >> $LOG
