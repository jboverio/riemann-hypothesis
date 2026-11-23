#!/usr/bin/env bash
# Runs a probe plan. Lines:  build <target> | variant <name> | reset | sh <command...>
set -uo pipefail
plan="$1"
out="probe-out/$(basename "$plan" .txt)"
mkdir -p "$out"
i=0
fail=0
while IFS= read -r line || [[ -n "$line" ]]; do
  line="${line%%#*}"
  read -r cmd arg rest <<<"$line" || true
  [[ -z "${cmd:-}" ]] && continue
  i=$((i + 1))
  case "$cmd" in
    build)
      log="$out/$(printf %02d "$i")-${arg##*.}.log"
      echo "::group::build $arg"
      /usr/bin/time -v lake build -v "$arg" >"$log" 2>&1
      rc=$?
      echo "probe-rc=$rc" >>"$log"
      [[ $rc != 0 ]] && fail=1
      grep -aE "Built |error|took [0-9.]+s$|probe-rc=|Elapsed \(wall|Maximum resident|User time|System time|cumulative|^\s+[a-zA-Z ().-]+ [0-9.]+m?s$" "$log" | tail -80
      echo "::endgroup::"
      ;;
    variant)
      echo "== overlay variant $arg"
      cp -rv "probe/variants/$arg/." .
      ;;
    reset)
      git checkout -- src
      ;;
    sh)
      bash -c "${line#*sh }" 2>&1 | tee "$out/$(printf %02d "$i")-sh.log"
      ;;
    *) echo "unknown plan command: $cmd" >&2; fail=1 ;;
  esac
done <"$plan"
exit $fail
