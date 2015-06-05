#!/bin/bash
echo "Generating script"
scala genRunscript.scala > tmpRun.sh
echo "Running script"
./tmpRun.sh

