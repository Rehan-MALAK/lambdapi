#!/bin/sh

set -euf -o noclobber

dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
usage="Usage: $(basename "$0") [-b]
Set up git pre-commit hook.

Arguments:
  -b    Include compilation in hook.
"
sanity_only=true
while getopts 'bh' arg; do
    case "${arg}" in
        b) sanity_only='';;
        h) printf '%s' "${usage}"
           exit 0
           ;;
        *) printf 'Invalid option\\n'
           printf '%s' "${usage}"
           exit 1
           ;;
    esac
done

git_root="$(realpath "${dir}/../.git")"

hook_path="${git_root}/hooks/pre-commit"
hook_cmd=''
## Set hook command depending on cli arguments
if [ -n "${sanity_only}" ]; then
    hook_cmd='[ -z "$(make sanity_check)" ]'
else
    hook_cmd='[ -z "$(make sanity_check)" ] && make bin'
fi

if [ -f "${hook_path}" ]; then
    printf 'Pre-commit hook [%s] found.
Remove it or add the command
%s
' "${hook_path}" "${hook_cmd}"
    exit 1
fi

printf '#!/bin/sh\n%s\n' "${hook_cmd}" > "${hook_path}"
chmod 755 "${hook_path}"