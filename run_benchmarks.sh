#!/bin/bash

TOTALTIME=0

function runBenchmark {
    OUTPUT=`./princess -timeout=60000 $1 2>&1`
    if [[ $OUTPUT == *"VALID"* ]]
    then
	echo $1
	echo "VALID"
	TIME=`echo $OUTPUT | grep -m1 -Eo '[0-9]+ms' | head -n 1`
	echo $TIME
	TIMEINT=`echo $TIME | grep -oE '[0-9]*'`
	TOTALTIME=$[$TOTALTIME + $TIMEINT]
    else
	echo "???"
    fi
}

for ARG in $*
do
    runBenchmark $ARG
done
echo "Total time: $TOTALTIME"




