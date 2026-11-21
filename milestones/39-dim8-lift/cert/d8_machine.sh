#!/bin/bash
# One-shot setup and launch of a level-116 certificate worker (milestone 39) on a fresh Ubuntu machine
# or a cloud session. Idempotent: rerun it after a reboot or crash; finished certificates are skipped.
#
#   INDEX=0-15 WORKERS=200 bash d8_machine.sh            # shares 0..15 of 200
#
# Environment:
#   INDEX     share list for prod_d8.py --index (e.g. 7, 0-15, 3,9,12)          required
#   WORKERS   total number of shares (prod_d8.py --workers)                      default 200
#   PROCS     parallel jobs           default: min(cores - 1, MEM_GB / 5)
#   MEM_GB    memory budget in GB     default: 85% of MemTotal
#   PUBLISH   1 = push results to refs/heads/xfer/d8/<NAME> (needs git push access)   default 1
#   NAME      published ref name                                                  default w<first index>
#   REPO      checkout directory      default: the repository this script is in, else ~/Snake-in-the-box-in-9
#   HOURS     stop taking new jobs after this many hours                         default unlimited
#   ONLY      comma list of cube masks to certify instead of the shares (tests)
# Logs: ~/d8.log (worker), ~/d8_setup.log. Stop gracefully: touch ~/d8work/STOP.
set -euo pipefail
: "${INDEX:?set INDEX, e.g. INDEX=0-15}"
WORKERS=${WORKERS:-200}; PUBLISH=${PUBLISH:-1}; HOURS=${HOURS:-1000000}
HERE=$(cd "$(dirname "$0")" && pwd)
if [ -z "${REPO:-}" ]; then
  if git -C "$HERE" rev-parse --show-toplevel >/dev/null 2>&1; then REPO=$(git -C "$HERE" rev-parse --show-toplevel)
  else REPO=$HOME/Snake-in-the-box-in-9; fi
fi
LEAN=/opt/lean-4.35.0-linux/bin/lean
exec 3>>"$HOME/d8_setup.log"; log() { echo "$(date -u +%FT%TZ) $*" | tee /dev/fd/3; }

# 1. toolchain (the same steps as the cloud environment's setup script)
if ! command -v git >/dev/null || ! command -v unzip >/dev/null || ! command -v make >/dev/null; then
  log "apt: git curl unzip build-essential python3"
  (sudo -n true 2>/dev/null && S=sudo || S=) ; $S apt-get update -qq && $S apt-get install -y -qq git curl unzip build-essential python3 >/dev/null
fi
SUDO=; [ "$(id -u)" -ne 0 ] && SUDO=sudo
if [ ! -x /usr/local/bin/cadical ]; then
  log "building cadical 2.1.3"
  $SUDO rm -rf /opt/cadical-2.1.3
  $SUDO git clone -q --depth 1 --branch rel-2.1.3 https://github.com/arminbiere/cadical /opt/cadical-2.1.3
  (cd /opt/cadical-2.1.3 && $SUDO ./configure >/dev/null && $SUDO make -j"$(nproc)" >/dev/null)
  $SUDO cp /opt/cadical-2.1.3/build/cadical /usr/local/bin/cadical
fi
if [ ! -x "$LEAN" ]; then
  log "installing lean 4.35.0"
  (cd /tmp && curl -sSL --retry 3 -o lean435.zip https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.zip \
   && $SUDO unzip -q -o lean435.zip -d /opt && rm lean435.zip)
fi
"$LEAN" --version | grep -q "4.35.0" || { log "wrong lean version"; exit 1; }

# 2. repository at the tip of research/unconditional-241 (fetched by name only)
if [ ! -d "$REPO/.git" ]; then
  log "cloning into $REPO"
  git clone -q --single-branch --branch research/unconditional-241 https://github.com/hironaka-iori/Snake-in-the-box-in-9 "$REPO"
fi
cd "$REPO"
git fetch -q origin research/unconditional-241
if [ -z "$(git status --porcelain --untracked-files=no)" ]; then git checkout -q -B research/unconditional-241 FETCH_HEAD; fi
log "repo at $(git log --oneline -1)"

# 3. Lean stacks: the plain stack (used by the exporters) and the 4.35 module stack (used by the certificates)
M=milestones/39-dim8-lift
if [ ! -f $M/lean/build/RenN.olean ] || [ ! -f $M/lean/build/Final.olean ]; then
  log "building the plain stack"; bash $M/lean/build.sh >> "$HOME/d8_setup.log" 2>&1
fi
STACK=$HOME/d8stack
if [ ! -f $STACK/build/Final.olean ]; then
  log "building the module stack"; python3 $M/cert/prod_d8.py setup --stack "$STACK" >> "$HOME/d8_setup.log" 2>&1
fi

# 4. launch (resumes from ~/d8work/manifest.jsonl)
if pgrep -f "prod_d8.py run" >/dev/null; then log "worker already running"; exit 0; fi
CORES=$(nproc); MEMT=$(awk '/MemTotal/{print int($2/1048576)}' /proc/meminfo)
MEM_GB=${MEM_GB:-$((MEMT * 85 / 100))}
P=$(( CORES - 1 )); Q=$(( MEM_GB / 5 )); PROCS=${PROCS:-$(( P < Q ? P : Q ))}; [ "$PROCS" -lt 1 ] && PROCS=1
ARGS=(run --stack "$STACK" --work "$HOME/d8work" --index "$INDEX" --workers "$WORKERS" --procs "$PROCS" --mem-gb "$MEM_GB" --hours "$HOURS")
[ -n "${NAME:-}" ] && ARGS+=(--name "$NAME")
[ -n "${ONLY:-}" ] && ARGS+=(--only "$ONLY")   # tests: certify just these cubes
[ "$PUBLISH" = 1 ] && ARGS+=(--publish)
log "launch: prod_d8.py ${ARGS[*]}"
nohup python3 $M/cert/prod_d8.py "${ARGS[@]}" >> "$HOME/d8.log" 2>&1 &
log "worker pid $!"
