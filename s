set program lambdapi.bc
set argument check tests/OK/rehan2.lp
so sbhandle
run
set print_depth 500
set print_length 10000
load_printer ./_build/default/src/core/.core.objs/byte/core__Timed.cmo
load_printer ./_build/default/src/core/.core.objs/byte/core__Mydebugocd.cmo
so s2
