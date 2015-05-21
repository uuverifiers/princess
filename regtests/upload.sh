#!/bin/bash
echo "Transfering tests..."
scp results.html petba168@celsius.it.uu.se:public_html/breu/
echo "Transfering logs..."
scp logs/*.log petba168@celsius.it.uu.se:public_html/breu/logs/