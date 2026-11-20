#!/bin/sh
# Build the Coq side of the virtualization port (needs Rocq 9).
set -e
C=$(cd "$(dirname "$0")" && pwd)
for f in Lang EPT VMCS VMX Trap; do
  rocq compile -Q "$C" VCoq "$C/$f.v"
done
