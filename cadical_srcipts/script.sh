#!/bin/bash

TOTAL=0
COUNT=0
MAX=0
LIMIT=10   # run at most 10 files

for f in UUF125.538.100/*; do
    [ -f "$f" ] || continue
    if [ "$COUNT" -ge "$LIMIT" ]; then
      break
    fi

    # Start time in nanoseconds
    start=$(date +%s%N)
    cadical "$f" > /dev/null 2>&1
    end=$(date +%s%N)

    # Convert to milliseconds
    t=$(( (end - start) / 1000000 ))

    echo "$(basename "$f"): $t ms"

    TOTAL=$((TOTAL + t))
    COUNT=$((COUNT + 1))

    # Update max
    if [ "$t" -gt "$MAX" ]; then
        MAX=$t
    fi
done

if [ "$COUNT" -gt 0 ]; then
    AVG=$((TOTAL / COUNT))
    echo "--------------------------------"
    echo "Files run: $COUNT"
    echo "Average runtime: $AVG ms"
    echo "Maximum runtime: $MAX ms"
else
    echo "No CNF files found."
fi
