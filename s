set program lambdapi.bc
set argument check tests/test.lp --verbose 3 --debug ceirstuwx
br @ Core__Handle 94
br @ Core__Handle 116
br @ Core__Handle 146
run
set print_depth 500
set print_length 10000
load_printer ./_build/default/src/core/.core.objs/byte/core__Timed.cmo
load_printer ./_build/default/src/core/.core.objs/byte/core__Mydebugocd.cmo
so s2
