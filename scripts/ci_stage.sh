#!/usr/bin/env bash
# One job of the staged CI build: unpack the outputs of the earlier stages (stage-in/*.tar.zst), build this job's
# targets from scripts/ci_plan.py, and pack the outputs it produced into stage-out.tar.zst for the later stages.
# Lake's per-module *.setup.json files are not packed: Lake writes them before each compile and does not need them to
# treat a module as up to date. usage: ci_stage.sh STAGE JOB STAGES JOBS
set -Eeuo pipefail
stage=$1 job=$2 stages=$3 jobs=$4

# download-artifact puts each artifact in its own folder: stage-in/<artifact>/stage-out.tar.zst
if [[ -d stage-in ]]; then
  find stage-in -name '*.tar.zst' | sort | while read -r f; do zstd -dc "$f" | tar -x; done
  rm -rf stage-in
fi

python3 scripts/ci_plan.py --stages "$stages" --jobs "$jobs" --summary
mapfile -t targets < <(python3 scripts/ci_plan.py --stages "$stages" --jobs "$jobs" --stage "$stage" --job "$job")
echo "stage $stage, job $job: ${#targets[@]} targets"

touch .stage-marker
sleep 1
if (( ${#targets[@]} )); then
  lake build "${targets[@]}" 2>&1 | tee stage-build.log
  if grep -E "declaration uses .sorry." stage-build.log; then
    echo "::error::The build reported a sorry."
    exit 1
  fi
fi

find .lake/build -type f ! -name '*.setup.json' -newer .stage-marker -print0 \
  | tar --null -T - -cf - | zstd -T0 -3 -q -o stage-out.tar.zst
find .lake/build -name '*.setup.json' -delete
ls -l stage-out.tar.zst
