loadScript('scripts.js')
eth.sendTransaction({from: primary, to: alice, value: web3.toWei(1, "ether")})
loadScript('rps_v1_dep.js')
rps.player_input.sendTransaction(1, {from: alice, value: web3.toWei(1, "ether"), gas: 300000})
rps.player_input.sendTransaction(2, {from: bob, value: web3.toWei(1, "ether"), gas: 300000})
rps.finalize.sendTransaction({from: alice, gas: 300000})