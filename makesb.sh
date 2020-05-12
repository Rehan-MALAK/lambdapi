#!/bin/bash -
set -o nounset                              # Treat unset variables as an error

breakpoints=(
  "count_products src/core/basics.ml"
  "get_args src/core/basics.ml"
  "add_args src/core/basics.ml"
  "make_meta src/core/basics.ml"
  "occurs src/core/basics.ml"
  "get_metas src/core/basics.ml"
  "has_metas src/core/basics.ml"
  "distinct_vars src/core/basics.ml"
  "unbind src/core/ctxt.ml"
  "type_of src/core/ctxt.ml"
  "to_prod src/core/ctxt.ml"
  "unfold src/core/ctxt.ml"
  "add src/core/env.ml"
  "find src/core/env.ml"
  "to_prod_box src/core/env.ml"
  "to_prod src/core/env.ml"
  "vars src/core/env.ml"
  "to_tbox src/core/env.ml"
  "to_ctxt src/core/env.ml"
  "infer src/core/infer.ml"
  "check src/core/infer.ml"
  "init src/core/proof.ml"
  "finished src/core/proof.ml"
  "pp_goals src/core/proof.ml"
  "get_implicitness src/core/scope.ml"
  "scope src/core/scope.ml"
  "scope_term src/core/scope.ml"
  "scope_rule src/core/scope.ml"
  "scope_rw_patt src/core/scope.ml"
  "create_sign src/core/sig_state.ml"
  "remove_pp_hint src/core/sig_state.ml"
  "remove_pp_hint_eq src/core/sig_state.ml"
  "add_symbol src/core/sig_state.ml"
  "add_binop src/core/sig_state.ml"
  "add_builtin src/core/sig_state.ml"
  "find src/core/sign.ml"
  "mem src/core/sign.ml"
  "loaded src/core/sign.ml"
  "new_sym src/core/sign.ml"
  "dummy src/core/sign.ml"
  "add_rule src/core/sign.ml"
  "add_ident src/core/sign.ml"
  "add_symbol src/core/sign.ml"
  "add_builtin src/core/sign.ml"
  "add_unop src/core/sign.ml"
  "add_binop src/core/sign.ml"
  "check_rule src/core/sr.ml"
  "handle_tactic src/core/tactics.ml"
  "check src/core/typing.ml"
  "infer_constr src/core/typing.ml"
  "infer src/core/typing.ml"
  "sort_type src/core/typing.ml"
  "solve src/core/unif.ml"
  "eq src/core/unif.ml"
)

function uppercasefirst ()
{
  word=$1
  first=${word:0:1}
  firstupper=${first^^}
  wordwithoutfirst=${word:1}
  echo "${firstupper}${wordwithoutfirst}"
}

function where_is ()
{
  pre=$1
  func=$2
  post=$3
  file=$4
  line=$(grep -n -e "$pre $func$post" -e "$pre rec $func$post" $file | tail -n 1 | cut -d':' -f1)
  echo $line
}

function where_is_let ()
{
  func=$1
  file=$2
  where_is "^let" $func " " $file
}

rm -fv sb*

# for br in P_symbol P_rules P_definition P_theorem P_query ; do
for br in P_definition ; do
  line=$(where_is "|" "$br" "(" "src/core/handle.ml")
  brcmd="br @ Core__Handle $line"
  echo "$brcmd" >> sbhandle
done

for br in "${breakpoints[@]}" ; do
  func=$(echo $br | awk '{print $1}')
  file=$(echo $br | awk '{print $2}')
  module=$(basename $file .ml)
  moduleuppercase=$(uppercasefirst $module)
  coremodule=Core__$moduleuppercase
  line=$(where_is_let $func $file)
  brcmd="br @ $coremodule $line"
  echo "$brcmd" >> sb$module
done
# line=
# breakpoint="br @ Core__Basics $line"

# echo ${breakpoint[*]}
