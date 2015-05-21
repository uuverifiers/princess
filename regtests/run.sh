#!/bin/bash
echo "Generating script"
scala genRunscript.scala > tmpRun.sh
echo "Runnign script"
./tmpRun.sh

