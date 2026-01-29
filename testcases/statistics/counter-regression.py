#!/bin/python3

import json
import numpy
import re
from sklearn.linear_model import LinearRegression
from sklearn.preprocessing import PolynomialFeatures
from operator import itemgetter

filename = "counter-stats.txt"

counterFile = open(filename, 'r')

print(f"Loading file {filename}")

counterRecords = list()
curSMTFile = ''

while True:
    line = counterFile.readline()
    if not line:
        break

    if line.startswith('Loading'):
        name = re.search("Loading (.*) \.\.\.", line)
        curSMTFile = name.group(1)
    else:
        counters = json.loads(line)
        counters['filename'] = curSMTFile
        counterRecords.append(counters)

counterFile.close()

print(f"Number of samples read: {len(counterRecords)}")

fields = list()

for counters in counterRecords:
    for n in counters.keys():
        if n != 'Milliseconds' and n != 'filename' and not (n in fields):
            fields.append(n)

fieldNum = len(fields)

print(f"Number of fields: {fieldNum}")

runtimes = list()
counterArrays = list()

for counters in counterRecords:
    runtimes.append(counters['Milliseconds'])
    rec = map(lambda n: counters.get(n, 0), fields)
    counterArrays.append(numpy.array(list(rec)))

model = LinearRegression(fit_intercept=False)

transformer = PolynomialFeatures(degree=3, include_bias=False)
transformer.fit(counterArrays)

counterArrays_ = counterArrays # transformer.transform(counterArrays)

model.fit(counterArrays_, runtimes)

print(f"R2: {model.score(counterArrays_, runtimes)}")

print("")

print(f"Milliseconds ~ {model.intercept_:.0f}", end='')

for i in range(0, fieldNum):
    print(f" + {model.coef_[i]:.3f} * {fields[i]}", end='')

print("")

pred = model.predict(numpy.array(counterArrays_))

relErrors = list()

for i in range(0, len(counterArrays)):
    if runtimes[i] > 3000:
        relErrors.append((counterRecords[i]['filename'], runtimes[i], pred[i], abs(runtimes[i] - pred[i]) / runtimes[i]))

for t in sorted(relErrors, key=itemgetter(3), reverse=True):
    print(t)


#    print(f"Predicted: {pred[i]:.0f}, actual: {runtimes[i]} \t({counterRecords[i]['filename']})")
