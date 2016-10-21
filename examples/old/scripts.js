function checkAllBalances() { 
  var i = 0; 
  web3.eth.accounts.forEach(function(id) {
    console.log("web3.eth.accounts["+i+"]: " + id + "\tbalance: " + web3.fromWei(web3.eth.getBalance(id), "ether") + " ether"); 
    i++;
  })
}; 

var primary = eth.accounts[0];
var alice = eth.accounts[1];
var bob = eth.accounts[2];