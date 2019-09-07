# Ethereum Smart Contracts in the Wild

This document looks at Ethereum smart contracts which were actually
running on the Ethereum blockchain in August 2019.

## Resources
There are a number of websites and articles which were helpful.

Firstly, http://etherscan.io lets you examine the Ethereum blockchain
in detail, including details of smart contracts ("Etherscan is the
leading Ethereum Blockchain Explorer. The core of Etherscan involves
extracting data from the Ethereum distributed ledger, indexing and
displaying the processed data in a concise and readable manner for the
masses and layperson."  ).

Users can upload smart contract source code to the website and
Etherscan will certify that they compile to particular bytecode
contracts, allowing you to examine the source code of at least some
contracts which you may find on the chain.

If you know the address of a smart contract then you can paste it into
the search bar at the top of the page and etherscan will give you lots
of information.

For example, the CryptoKitties contract has address 0x06012c8cf97bead5deae237070f9587f8e7a266d
and you can see information about it at https://etherscan.io/address/0x06012c8cf97bead5deae237070f9587f8e7a266d

![1](./CryptoKittiesInfo.png)

Note the link "Contract" near the centre of the image.  In this case it
has a green tick attached which means that the Solidity source of the contract is available,
and clicking on the link will show it to you:

![eh](./CryptoKittiesSource.png)


You can also go to https://etherscan.io/contractsVerified to see the last 500 contracts verified by Etherscan.

Etherscan also has a blog at https://medium.com/etherscan-blog/ which has some interesting articles.

----------------------------

There's an article talking about the usage of Ethereum smart contracts at
https://medium.com/@vikati/ranking-ethereum-smart-contracts-a27e6f622ac6

This contains links to pages showing the top 50 contracts by
[transactions](https://blockspur.com/ethereum_contracts/transactions),
["uniques"](https://blockspur.com/ethereum_contracts/uniques),
and [revenues](https://blockspur.com/ethereum_contracts/values).
Statistics are available for the most recent calendar month.

Unfortunately these pages are slightly broken:  the addresses of the
contracts are clickable and look as if they should show you more information
on the contract, but this doesn't work.  Instead I had to copy the URLs,
extract the contract addresses, and paste them into Etherscan to find out about the contracts.

There's a more detailed look at the most popular contracts for August 2019 [later](#popular-contracts-in-august-2019).

-----------------------

There's some more analysis of popularity of Ethereum contracts 
[here](https://blog.sfox.com/what-29-985-328-transactions-say-about-the-state-of-smart-contracts-on-ethereum-2ebdba4bea1c).

... and a site which tells you which contracts are currently using the most gas at https://ethgasstation.info/gasguzzlers.php.

Also, Google has large public databases of both
[Ethereum](https://cloud.google.com/blog/products/data-analytics/ethereum-bigquery-public-dataset-smart-contract-analytics
) and [Bitcoin](https://cloud.google.com/blog/products/gcp/bitcoin-in-bigquery-blockchain-analytics-on-public-data
) transactions which you can query yourself (although it might take some time to construct appropriate queries).

Rankings of Ethereum Dapps: https://www.stateofthedapps.com/rankings

-----------------------------

### Some Ethereum background

There are two Ethereum standards which are important for smart
contracts: [ERC-20](https://eips.ethereum.org/EIPS/eip-20) and
[ERC-721](https://eips.ethereum.org/EIPS/eip-721).  ERC-20 allows the
implementation of user-defined _token currencies_ on the Ethereum
chain and ERC-721 introduces non-fungible tokens which can be used to
represent ownership of some digital or physical asset.  To use either
of these you implement a smart contract which conforms to a specified
API which acts as the monetary policy.  For example in the case of
ERC-20 you implement a contract with functions which return the total
supply or the number of tokens owned by a specified individual, or
allow a user to transfer funds to another user, and so on.

Users may wish to trade one ERC-20 for another, and this can be done
using a _decentralised exchange_ (or _DEX_): these are generally
implemented as smart contracts.  


### Popular contracts in August 2019


================================================================
Top 50 contracts August 2019 by number of transactions

|Rank|Change|Address|Name|Symbol|ERC20|Transactions|Uniques|"Revenues" in Ether|"Revenues" in USD|
|----|------|-------|----|------|-----|------------|-------|-------------------|-----------------|
| 1|	N/A 		| 0x4f01001...|		|		|No 	|301,256	| 1	| 0.00 ETH	| 0.00 |
| 2|	-1 		| 0x2a0c0db...|Exchange	|		|No |	290,452	|17,889	|67,230.13 ETH	|$5,781,791|
| 3|	-1 		| 0xd1ceeee...|		|		|No |	|250,639	820	|34,972.39 ETH	$3,007,625
| 4|	+ 4 		| 0x8fdcc30...|CpcToken	|CPCT | 		|Yes| 	|147,724	10,396	0.00 ETH	0.00
| 5|	-2 		| 0x06012c8...|CryptoKitties	|CK| 	|Yes| 	|139,776	2,416	386.17 ETH	$33,211
| 6|	+ 926 		| 0x993e6d6...||No |	100,477	3,631	0.01 ETH	$1
| 7|	0 		| 0x8d12a19...|EtherDelta			|No |	91,653	10,593	26,086.14 ETH	$2,243,408
| 8|	+ 4 		| 0x5da8d37...|Tuzy Coin	TUC 		|Yes| 	90,009	1,788	0.00 ETH	0.00
| 9|	+ 47 		| 0x14fbca9...|MatchingMarket			|No |	77,747	859	0.00 ETH	0.00
| 10|	+ 196 		| 0x6090a6e...|Registrar			|No |	72,022	735	83.89 ETH	$7,215
| 11|	+ 1325 		| 0x0be3e6e...||No |	70,390	5,920	2,562.10 ETH	$220,341
| 12|	+ 54 		| 0x891f460...|VRT CHAIN TOKEN	VRT 		|Yes| 	65,770	9,819	0.00 ETH	0.00
| 13|	N/A 		| 0x62a364f...||No |	62,401	43,361	0.05 ETH	$4
| 14|	+ 1 		| 0xa15c7eb...|Pundi X Token	NPXS 		|Yes| 	61,421	7,637	0.00 ETH	0.00
| 15|	+ 3821 		| 0x08ceed1...|Electronic Energy...	E2C 	|Yes| 	58,200	5,407	0.00 ETH	0.00
| 16|	-10 		| 0x1ce7ae5...|TokenStore			|No |	54,623	3,429	1,542.42 ETH	$132,648
| 17|	+ 31014 	| 0x14ddda4...|FXPay		FXP 		|Yes| 	54,600	1,299	0.00 ETH	0.00
| 18|	+ 61 		| 0xb64ef51...|Storj		STORJ 		|Yes| 	54,006	47,294	0.00 ETH	$0
| 19|	+ 39 		| 0xba7435a...|AirdropToken	AIRDROP 	|Yes| 	52,841	55,723	0.02 ETH	$2
| 20|	+ 183 		| 0x1f772db...||No |	51,646	1,667	290.30 ETH	$24,966
| 21|	+ 24 		| 0x410af23...|CLEAR Token	CLEAR 		|Yes| 	49,540	489	0.00 ETH	0.00
| 22|	N/A 		| 0x9af285f...||No |	48,155	24,217	0.12 ETH	$11
| 23|	+ 7 		| 0xe7d7b37...|empowr	EMPR 			|Yes| 	44,634	3,642	0.69 ETH	$59
| 24|	+ 4 		| 0x7415c7b...|Coinage				|Yes| 	41,827	13,891	279,296.27 ETH	$24,019,480
| 25|	-6 		| 0xa52e014...||No |	40,295	385	7,190.89 ETH	$618,416
| 26|	+ 12 		| 0x827727b...||No |	39,532	4	0.00 ETH	0.00
| 27|	+ 75 		| 0x4f833a2...||No |	39,069	668	0.00 ETH	0.00
| 28|	-12 		| 0xe41d248...|ZRX	ZRX 			|Yes| 	38,441	18,129	0.00 ETH	0.00
| 29|	+ 40 		| 0x0d8775f...|BAT	BAT 			|Yes| 	38,213	14,363	0.00 ETH	0.00
| 30|	+ 31 		| 0xd26114c...|OmiseGO	OMG 			|Yes| 	38,178	17,458	0.00 ETH	0.00
| 31|	+ 36 		| 0x8912358...|Wisdom chain	Wdc 		|Yes| 	37,999	7,007	0.00 ETH	0.00
| 32|	+ 51 		| 0x7b45a57...||No |	37,961	2,027	128,802.98 ETH	$11,077,056
| 33|	+ 52 		| 0x12459c9...|Exchange			|No |	37,385	70	0.01 ETH	$1
| 34|	-1 		| 0xfa52274...||No |	36,910	10,368	324,224.21 ETH	$27,883,282
| 35|	+ 35 		| 0x0b95993...||No |	35,185	298	79.94 ETH	$6,875
| 36|	N/A 		| 0x105631c...||No |	33,753	11,734	0.00 ETH	0.00
| 37|	N/A 		| 0x896b516...||No |	33,314	6	0.00 ETH	0.00
| 38|	N/A 		| 0xd97e471...|EmcoToken	EMCO 		|Yes| 	32,917	3,061	0.00 ETH	0.00
| 39|	N/A 		| 0x13552c7...||No |	32,841	3,713	0.00 ETH	0.00
| 40|	+ 3 		| 0xd73be53...|BlockchainCuties BC 		|Yes| 	32,327	845	14.89 ETH	$1,280
| 41|	+ 9777 		| 0x8432a5a...|Gabro Token	GBO. 		|Yes| 	32,212	44	0.00 ETH	0.00
| 42|	-15 		| 0x9554efa...||No |	31,927	7,228	13,189.37 ETH	$1,134,286
| 43|	+ 4 		| 0xd77bcd9...|GA_chain	GA 		|Yes| 	31,484	109	0.00 ETH	0.00
| 44|	+ 27 		| 0xc02aaa3...|Wrapped Ether	WETH 		|Yes| 	30,118	6,402	191,654.28 ETH	$16,482,268
| 45|	N/A 		| 0xa3c1e32...|Controller			|No |	30,062	2	0.00 ETH	0.00
| 46|	+ 7 		| 0x4672bad...|Dropil	DROP 			|Yes| 	29,934	5,145	0.00 ETH	0.00
| 47|	-6 		| 0x798abda...||No |	29,850	1	0.00 ETH	0.00
| 48|	+ 208 		| 0x49a8ade...|STOCK	STO 			|Yes| 	28,952	713	0.00 ETH	0.00
|  49|	+ 41 		| 0x0777f76...||No |	28,410	1,451	487.16 ETH	$41,896
| 50|	+ 4273 		| 0x0c6373e...|NoteOfExchange	NOE 		|Yes| 	28,311	21,983	19.25 ETH	$1,655


Of top 50, 24 involve ERC-20
Hundreds/thousands of ERC-20 tokens: https://bloxy.info/list_tokens/ERC20

CPCtoken: (CPC Chain: Distributed Internet of Things.  https://cpchain.io/ unrelated?)
TuzyCoin: just a coin
VRT chain token: Virtual reality platform

E2C: https://electronicenergycoin.com/  Green energy platform

FXPay: Foreign Exchange.  fxpay.io

Storj: Decentralised file storage. https://coincentral.com/storj-beginners-guide/ storj.io
Coins used for payments to farmers who contribute storage space/bandwidth

Airdrop: In general, free coins to increase public interest in some new offering/service.
https://en.wikipedia.org/wiki/Airdrop_(cryptocurrency)

ClearToken: https://clearfoundation.co.nz/

Gabro: https://icobench.com/ico/gabro  Aggregating/exchanging loyalty rewards. 

Quite a lot of these don't seem to exist.


CryptoKitties / BlockChainCuties


================================================================
0x4f01001cf69785d4c37f03fd87398849411ccbba is number one, but I can't 
work out what it is.

---------

https://etherscan.io/address/0xd1ceeeeee83f8bcf3bedad437202b6154e9f5405#code
https://dice2.win/
Provably fair: roll a dice, flip a coin etc.  House takes 1%

----------
0x993e6d6c557ca24a00da507f56bda599a9886a44

Omniscience Dedication Financial

Can't see the contract.

Google takes us to https://www.reddit.com/r/ethereum/comments/9ueh6i/what_is_this_token_that_are_taking_11_of_the/
"It’s a securitised asset which is being launched on ethereum and distributed to its holders"

----------

Exchange:
Contract 0x2a0c0DBEcC7E4D658f48E01e3fA353F44050c208
42,122.231567773606290509 Ether 
Contract at https://etherscan.io/address/0x2a0c0dbecc7e4d658f48e01e3fa353f44050c208#code

Exchange wallet: lots of comments about theft.  
https://etherscan.io/address/0x2a0c0dbecc7e4d658f48e01e3fa353f44050c208#comments
IDEX: distributed exchange for trading between different token currencies.

Contracts are available.

-----------

EtherDelta: decentralized trading platform for Ether and Ethereum-based tokens, single smart contract.
Contract at https://etherscan.io/address/0x8d12a197cb00d4747a1fe03395095ce2a5cc6819
Requires trust, could steal private key from browser session.

https://hackernoon.com/how-one-hacker-stole-thousands-of-dollars-worth-of-cryptocurrency-with-a-classic-code-injection-a3aba5d2bff0



-------------

MatchingMarket: 0x39755357759ce0d7f32dc8dc45414cca409ae24e
eth2dai


OasisDex: dsitributed exchange, closing down.
New contract at 

See also https://etherscan.io/accounts/label/maker 

Maker is a decentralized autonomous organization on the Ethereum
blockchain seeking to minimize the price volatility of its own stable
token — the Dai — against the U.S. Dollar.  

---------------

Registrar: 0x6090a6e47849629b7245dfa1ca21d94cd15878ef

Ethereum name service. Contract available

---------------

https://etherscan.io/address/0x0be3e6e3d9e99036ccce4fd0b692016de860aa62

FCK Dice: https://www.stateofthedapps.com/dapps/fck
Contract available.


----------------

https://etherscan.io/address/0x62a364f7cba3be8fc9dcfdde12cabec8244af381
Don't know, no contract source.  

62,401 transactions


----------------

TokenStore

https://etherscan.io/address/0x1ce7ae555139c5ef5a57cc8d814a867ee6ee33d8
DEX

https://token.store/

----------------

https://etherscan.io/address/0x1f772db718238d8413bad9b309950a9c5286fd71
No contract, don't know.

----------------

https://etherscan.io/address/0x9af285f84645892dd57ae135af6e97f952a5922c
No contract, don't know.

----------------
https://etherscan.io/address/0xa52e014b3f5cc48287c2d483a3e026c32cc76e6d

https://etherscan.io/accounts/label/etheroll

Dice roll

----------------
https://etherscan.io/address/0x827727b4c3f75ea6eb6bd2cc256de40db2b13665
No contract, don't know.

----------------
https://blockspur.com/ethereum_contracts/0x4f833a24e1f95d70f028921e27040ca56e09ab0b

https://0x.org/
3800 lines of solidity.

Another DEX I think.

----------------

https://etherscan.io/address/0x7b45a572ea991887a01fd919c05edf1cac79c311
R1Exchange

See https://blog.smartdec.net/oneroot-smart-contracts-security-analysis-3958263fbe67

https://www.oneroot.io/



----------------
https://etherscan.io/address/0xfa52274dd61e1643d2205169732f29114bc240b3

No source, but see
https://www.reddit.com/r/ethereum/comments/60mmb8/anybody_know_what_contract_this_is_my_friends/


"contract 0xFa52274DD61E1643d2205169732f29114BC240b3 seems to be an
 ETH/ETC splitter contract, created on July 28.
 0x267be1c1d684f78cb4f6a176c4911b741e4ffdc0 is the ETH forward-to
 address, 0xb68884048cdd9f3d67a94c9586068c024d8679ca - ETC forward-to
 address.  Kraken announced their ETH/ETC automated splitter on the
 same day.  Anyway, this first contract you linked is not a
 mixer. It's Kraken's internal implementation of a splitter, provided
 for people who didn't want to fiddle themselves with AmIOnTheFork or
 ReplaySafeSplit by Timon Rapp (/u/_tr).  level 2"

----------------
0x0b95993A39A363d99280Ac950f5E4536Ab5C5566
Possibly another exchange.


----------------
https://etherscan.io/address/0x105631c6cddba84d12fa916f0045b1f97ec9c268
No idea.

----------------
https://etherscan.io/address/0x896b516eb300e61cfc96ee1de4b297374e7b70ed
Not sure:  see https://etherscan.io/token/0x98976a6dfaaf97b16a4bb06035cc84be12e79110?a=0x896b516eb300e61cfc96ee1de4b297374e7b70ed
Has to do with MYOUToken


----------------
https://etherscan.io/address/0x13552c7cc9ce39af665955412faa08f0e6555a29

Token tracker -> NineGods.  
https://etherscan.io/token/0x13552c7cc9ce39af665955412faa08f0e6555a29

----------------
0xa3C1E324CA1ce40db73eD6026c4A177F099B5770

"Controller".  No idea what it does, but 20M calls from 700,000 callers.
Source is visible.

----------------

https://etherscan.io/address/0x798abda6cc246d0edba912092a2a3dbd3d11191b

Name: ConversionRates

================================================================

Top by revenues.  

Splitter again.


----------------
https://etherscan.io/address/0x6fc82a5fe25a5cdb58bc74600a40a69c065263f8
Fiat gateway (-> cash)
No source


----------------
Wrapped Ether
https://blockspur.com/ethereum_contracts/0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2

----------------
https://etherscan.io/address/0x07c62a47ebe0fa853bb83375e488896ce71266df#code

MultiSigContractWithDailyLimit

----------------
https://etherscan.io/address/0x7b45a572ea991887a01fd919c05edf1cac79c311

R1Exchange

----------------
https://etherscan.io/address/0x2a0c0dbecc7e4d658f48e01e3fa353f44050c208

IDEX1


----------------
https://etherscan.io/address/0xabbb6bebfa05aa13e908eaa492bd7a8343760477

ReplaySafeSplit


----------------
https://etherscan.io/address/0xff6b1cdfd2d3e37977d7938aa06b6d89d6675e27

AllBit DEX

----------------
https://etherscan.io/address/0xd9b20CFED69e76acAE3FA1C2Ee1faAFAfcb41f55

No idea, but > $5M "revenue"


----------------
https://etherscan.io/address/0xd1ceeeeee83f8bcf3bedad437202b6154e9f5405

Dice2Win again

----------------
https://etherscan.io/address/0x02caceb4bfc2669156b2eb3b4d590e7ac10a4e73#code

DistributeETH


----------------
https://etherscan.io/address/0x209c4784ab1e8183cf58ca33cb740efbf3fc18ef

Poloniex Exchange.  No source.

----------------
https://etherscan.io/address/0xd64979357160e8146f6e1d805cf20437397bf1ba

SaiProxyCreateAndExecute

https://www.reddit.com/r/ethereum/comments/6feib0/introducing_sai_makerdais_first_generation/
"Introducing Sai, MakerDai's first generation stablecoin"

----------------
https://etherscan.io/address/0x0b65c5f6f3a05d6be5588a72b603360773b3fe04
No idea

----------------
https://etherscan.io/address/0x94e17901b6dfae329c63edd59447e2882e55aca6
No idea

----------------
https://etherscan.io/address/0x9554efa1669014c25070bc23c2df262825704228#code
ReplaySafeSplit again.


----------------
https://etherscan.io/address/0x1fe1751d26fda707ad29894a866f7aa3e1ffe628
Reversible Ether

https://programtheblockchain.com/posts/2018/06/09/reversible-ether/

"Someone should come along and issue an ERC20 called "Reversible Ether"
that is 1:1 backed by ether but has a DAO that can revert transfers
within N days."

----------------
https://etherscan.io/address/0x7bd0ce1c4c0bb344bbc71e8364845eeb211b99c4

HLHTTOKEN?
