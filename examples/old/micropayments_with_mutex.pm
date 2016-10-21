//
pta
//mdp

const int big_payment = 10;
const int max_asks = 20;
const int max_blockchain = 10;
const int max_protocol_time = 1000;
const double p = 1 / big_payment;
//const double q;							//Probability of mauling the transaction.

module blockchain
	trans_payment : [-2..3] init 0;				//-2: spent, -1: invalidated, 0: unsent, 1: broadcasted, 2: accepted, 3: mauled and accepted
	trans_to_seller : [-2..3] init 0;
	trans_to_buyer : [-2..3] init 0;
	payment_clock : clock;
	to_seller_clock : clock;
	to_buyer_clock : clock;
	general_clock : clock;

	invariant
	    (trans_payment=1 => payment_clock <= max_blockchain) &
	    (trans_to_seller=1 => to_seller_clock <= max_blockchain) &
	    (trans_to_buyer=1 => to_buyer_clock <= max_blockchain) &
	    ((trans_payment!=1 & trans_to_seller!=1 & trans_to_buyer!=1) => general_clock=0)
	endinvariant

	[broadcast_trans_payment] true -> (trans_payment'=1) & (payment_clock'=0);
	[broadcast_trans_to_seller] true -> (trans_to_seller'=1) & (to_seller_clock'=0);
	[broadcast_trans_to_buyer] true -> (trans_to_buyer'=1) & (to_buyer_clock'=0);

	[trans_payment_accept] trans_payment=1 -> (trans_payment'=2) & (general_clock'=0);
	[trans_payment_accept] trans_payment=1 -> (trans_payment'=3) & (general_clock'=0);
	[trans_to_seller_accept] trans_to_seller=1 & trans_payment>=2 -> 
		(trans_to_seller'=2) & (trans_payment'=-2) & (general_clock'=0);
	[trans_to_seller_accept] trans_to_seller=1 & trans_payment>=2 -> 
		(trans_to_seller'=3) & (trans_payment'=-2) & (general_clock'=0);
	[trans_to_buyer_accept] trans_to_buyer=1 & trans_payment>=2 -> 
		(trans_to_buyer'=2) & (trans_payment'=-2) & (general_clock'=0);
	[trans_to_buyer_accept] trans_to_buyer=1 & trans_payment>=2 -> 
		(trans_to_buyer'=3) & (trans_payment'=-2) & (general_clock'=0);
	[] trans_to_seller=1 & trans_payment<=1 -> (trans_to_seller'=-1) & (general_clock'=0);
	[] trans_to_buyer=1 & trans_payment<=1 -> (trans_to_buyer'=-1) & (general_clock'=0);
endmodule

module bank
	seller_cash : [0..(max_asks+1)] init 0;
	buyer_cash : [-(max_asks+1)..(max_asks+1)] init 0;

	[trans_payment_accept] buyer_cash>=-max_asks -> (buyer_cash'=buyer_cash-1);
	[trans_to_buyer_accept] buyer_cash<=max_asks -> (buyer_cash'=buyer_cash+1);
	[trans_to_seller_accept] seller_cash<=max_asks -> (seller_cash'=seller_cash+1);
endmodule

module channel
	ask_product : [-1..1] init 0;									//-1: invalid, 0: unsent, 1: sent
	product : [-1..1] init 0;
	payment : [-1..1] init 0;
	payment_accepted : [-1..1] init 0;

	[send_ask_product] true -> (ask_product'=1);
	[bad_ask_product] true -> (ask_product'=-1);
	[read_ask_product] ask_product=1 -> (ask_product'=0);
	[send_product] true -> (product'=1);
	[read_product] product=1 -> (product'=0);
	[send_payment] true -> (payment'=1);
//	[bad_payment] true -> (payment'=-1) & (channel_state_changed'=true);
	[read_payment] payment=1 -> (payment'=0);
	[send_payment_accepted] true -> (payment_accepted'=1);
	[read_payment_accepted] payment_accepted=1 -> (payment_accepted'=0);
endmodule

module honest_seller
	seller_state : [-2..5] init 0;
	issued : [0..max_asks+1] init 0;
	mutex : bool init false;

	[read_ask_product] seller_state=0 & issued<max_asks & trans_payment>=2 -> (seller_state'=1);		//Seller issues the product and asks for payment.
	[send_product] seller_state=1 & issued<=max_asks -> (issued'=issued+1) & (seller_state'=2);		//Send the product.
	[read_payment] seller_state=2 ->									//Lottery.
		(1-p) : (seller_state'=5) & (mutex'=true) +							//Seller loses.
		p : (seller_state'=3) & (mutex'=true);								//Seller wins.
	[broadcast_trans_to_seller] seller_state=3 -> (seller_state'=4) & (mutex'=false);			//Broadcasting the transaction.
	[] seller_state=4 & trans_to_seller>=2 -> (seller_state'=5);						//Transaction is accepted.
	[send_payment_accepted] seller_state=5 -> (seller_state'=0) & (mutex'=false);				//End iteration.

	[honest_seller_end] seller_state=0 & issued=max_asks -> (seller_state'=-1);				//End of the protocol - Ok.
	[honest_seller_end] seller_state=0 & ask_product=-1 -> (seller_state'=-1);				//Buyer left the protocol - Ok.
	[honest_seller_end] seller_state=2 & payment=-1 -> (seller_state'=-2);					//Wrong payment - Error.
	[honest_seller_end] seller_state=4 & trans_to_seller=-1 -> (seller_state'=-2);				//The transaction is invalidated - Error.
endmodule


module honest_buyer
	buyer_state : [-3..4] init 0;
	no_products : [0..max_asks+1] init 0;

	[bad_ask_product] buyer_state=0 -> (buyer_state'=-1);						//Buyer can left the protocol at any time.
	[broadcast_trans_to_buyer] buyer_state=-1 & trans_payment>=2 -> (buyer_state'=-2);		//At the end of the protocol redeem trans_payment.
	[honest_buyer_end] buyer_state=-1 & trans_payment<=0 -> (buyer_state'=-3);			//If cannot - just end.
	[honest_buyer_end] buyer_state=-2 & trans_to_buyer>=2 -> (buyer_state'=-3);			//If can - wait for trans_to_buyer acceptance.

	[broadcast_trans_payment] buyer_state=0 & trans_payment<=0 & no_products<max_asks -> true;	//Buyer broadcasts the transaction.
	[] buyer_state=0 & trans_payment>=2 & no_products<max_asks -> (buyer_state'=1);			//The transaction is already accepted.
	[send_ask_product] buyer_state=1 -> (buyer_state'=2);						//Ask for another product.
	[read_product] buyer_state=2 & no_products<=max_asks-> 
		(no_products'=no_products+1) & (buyer_state'=3);					//Consume product.
	[send_payment] buyer_state=3 -> (buyer_state'=4);						//Send payment.
	[read_payment_accepted] buyer_state=4 & payment_accepted=1 -> (buyer_state'=0);			//Move to the next iteration.
endmodule

module anti_deadlock
//	test : bool init true;
//	[] test -> (test'=true);
	[] true -> true;
endmodule

//module adv_buyer
//	[broadcast_trans_to_buyer] !mutex & trans_to_seller<=0 -> true;
//	[broadcast_trans_payment] !mutex & trans_payment<=0 -> true;
//
//	[send_ask_product] !mutex & ask_product=0 -> true;
//	[bad_ask_product] !mutex & ask_product=0 -> true;
//	[send_payment] !mutex & payment=0 -> true;
//	[bad_payment] !mutex & payment=0 -> true;
//	[read_payment_accepted] !mutex -> true;
//	[read_product] !mutex -> true;
//endmodule

//module adv_seller
//endmodule



rewards "profit_seller"											//Real profit equals: "profit_seller - max_asks.
	[honest_seller_end] issued<=max_asks : seller_cash * big_payment + (max_asks-issued);
endrewards
