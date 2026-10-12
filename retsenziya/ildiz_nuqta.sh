#!/bin/bash
# A yo'l: b=3, k=151..250 (k≢0): asosiy shox q_n ildizlarida (0,1/2] aniq nuqtaviy DFS, 9 parallel
cd "$(dirname "$0")/.."
LOG=retsenziya/ildiz_nuqta.log; : > $LOG
run(){ timeout 3600 ~/arsenal-venv/bin/python retsenziya/ildiz_nuqta.py $1 2>/dev/null | tail -1 >> $LOG; }
export -f run; export LOG
xargs -P 9 -L 1 bash -c 'run $0' < retsenziya/ildiz_k.txt
echo "ILDIZ-TUGADI" >> $LOG
