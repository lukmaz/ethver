loadScript('scripts.js')
loadScript('rps_v2_dep.js')

var choiceA = "1"
var nonceA = "nf31f09"
var commitmentA = "0x" + web3.sha3(alice + choiceA + nonceA, true)
0x9c6282885a630e8088883806cbd2297a954122e7602f4ee5d8a8337db734223d

var choiceB = "2"
var nonceB = "8sdh3r"
var commitmentB = "0x" + web3.sha3(bob + choiceB + nonceB, true)
0x3235de5fdf220f8b6635a46f19462c373f8ae5e297585cb824abb0c2d21e510d

rps.player_input.sendTransaction(commitmentA, {from: alice, value: web3.toWei(100, "finney"), gas: 1000000})
rps.player_input.sendTransaction(commitmentB, {from: bob, value: web3.toWei(100, "finney"), gas: 1000000})

rps.open.sendTransaction(choiceA, nonceA, {from: alice, value: 0, gas: 1000000})
rps.open.sendTransaction(choiceB, nonceB, {from: bob, value: 0, gas: 1000000})


rps.finalize.sendTransaction({from: alice, gas: 1000000})