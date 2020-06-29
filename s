set program lambdapi.bc
set argument check --debug t tests/pri.lp
so sbhandle
so sbtactics
run
set print_depth 500
set print_length 10000
load_printer ./_build/default/src/core/.core.objs/byte/core__Timed.cmo
load_printer ./_build/default/src/core/.core.objs/byte/core__Mydebugocd.cmo
so s2
