#!/bin/bash
# Fetch only our branch (a plain `git pull` fetches every refs/heads/*, including the multi-GB
# xfer/* certificate branches), rebase, push; retries on network errors.
set -u
B=research/unconditional-241
cd "$(dirname "$0")/../.."
for i in 1 2 3 4; do
  if timeout 300 git fetch -q origin "+refs/heads/$B:refs/remotes/origin/$B"; then break; fi
  sleep $((2**i))
done
git rebase -q --autostash "origin/$B" || exit 1
for i in 1 2 3 4; do
  if timeout 300 git push -q -u origin "$B"; then echo pushed; exit 0; fi
  sleep $((2**i))
done
exit 1
