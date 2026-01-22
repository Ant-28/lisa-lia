#!/bin/bash
ceil() {
    echo "define ceil(x) { if(x < 0) {return x + 1} \
        else {if(scale(x) == 0) {return x} \
        else {return x/1 + 1}}}; \
        ceil($1)" | bc
}
export HALF_RAM=$(ceil $( awk '/MemTotal/ { printf "%.3f", $2/1024/1024/2}' /proc/meminfo ))
export _JAVA_OPTIONS="-Xmx${HALF_RAM}g"
./mill Cooper