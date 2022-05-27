Following instructions from: https://github.com/brendangregg/FlameGraph

sudo dtrace -x ustackframes=100 -n 'profile-97 /pid == 92637  && arg1/ { @[ustack()] = count(); } tick-60s { exit(0); }' -o out.user_stacks
./stackcollapse.pl out.user_stacks > out.user_folded 
flamegraph.pl out.user_folded > profile.svg 


TODO:
  - Use `pgrep z3tracer` to automate the PID lookup
