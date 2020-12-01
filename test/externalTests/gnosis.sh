#!/usr/bin/env bash

# ------------------------------------------------------------------------------
# This file is part of solidity.
#
# solidity is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# solidity is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with solidity.  If not, see <http://www.gnu.org/licenses/>
#
# (c) 2019 solidity contributors.
#------------------------------------------------------------------------------
source scripts/common.sh
source test/externalTests/common.sh

verify_input "$1"
SOLJSON="$1"

function install_fn { npm install --package-lock; }
function compile_fn { npx truffle compile; }
function test_fn { npm test; }

function gnosis_safe_test
{
    OPTIMIZER_LEVEL=1
    CONFIG="truffle-config.js"

    truffle_setup https://github.com/cameel/safe-contracts.git v2_070

    sed -i 's|github:gnosis/mock-contract#sol_0_5_0|github:gnosis/mock-contract#master|g' package.json
    sed -i -E 's|"@gnosis.pm/util-contracts": "[^"]+"|"@gnosis.pm/util-contracts": "github:gnosis/util-contracts#solc-6"|g' package.json
    rm -f package-lock.json
    rm -rf node_modules/

    run_install install_fn
    replace_libsolc_call

    truffle_run_test compile_fn test_fn
}

external_test Gnosis-Safe gnosis_safe_test
