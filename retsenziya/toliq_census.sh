#!/bin/bash
# M16 #5 tuzatish: census + b=3 (k≤60) ni GCD_TEKSHIR=1 (izolyatsiyalangan nuqtalar + chegara ildizlari nuqtaviy) bilan qayta isbotlash, 9 parallel
cd "$(dirname "$0")/.."
LOG=retsenziya/toliq_census.log; : > $LOG
run(){ GCD_TEKSHIR=1 timeout 7200 ~/arsenal-venv/bin/python simvolik_isbot_flint.py $1 $2 2000 $3 $4 2>/dev/null | tail -1 >> $LOG; }
export -f run; export LOG
xargs -P 9 -L 1 bash -c 'run $0 $1 $2 $3' < retsenziya/toliq_vazifa.txt
echo "TOLIQ-TUGADI" >> $LOG
