Property based symbolic executor: manticore-verifier
====================================================
Manticore installs a separated CLI tool to do property based symbolic execution of smart contracts. ::

    $ manticore-verifier your_contract.sol

**manticore-verifier** initializes an emulated blockchain environment with a configurable set of
accounts and then sends various symbolic transactions to the target contract containing property methods.
If a way to break a property is found the full transaction trace to reproduce the behaivor is provided.
A configurable stopping condition bounds the exploration, properties not failing are considered to pass.


Writing properties in {Solidity/ Vyper}
---------------------------------------
**manticore-verifier** will detect and test property methods written in the 
original contract language. A property can be written in the original language
by simply naming a method in a specific way. For example methods names starting with ```crytic_```.

.. code-block:: javascript

    function crytic_test_true_property() view public returns (bool){
            return true;
        }

You can select your own way to name property methods using the ``--propre`` commandline argument. ::

    --propre PROPRE       A regular expression for selecting properties

Normal properties
^^^^^^^^^^^^^^^^^
In the most common case after some precondition is met some logic property must always be true.
Normal properties are property methods that must always return true (or REVERT). 


Reverting properties
^^^^^^^^^^^^^^^^^^^^
Sometimes it is difficult to detect that a revert has happened in an internal transaction. 
manticore-verifier allows to test for ALWAYS REVERTing property methods.
Revert properties are property methods that must always REVERT.
Reverting property are any property method that contains "revert". For example: 

.. code-block:: javascript

    function crytic_test_must_always_revert() view public returns (bool){
            return true;
    }


Selecting a target contract
===========================
**manticore-verifier** needs to be pointed to a the target contract containing any number of property methods.
The target contract is the entry point of the exploration. It needs to initilize any internal structure or external contracts to a correct initial state. All methods of this contract matching the property name criteria will be tested. ::

   --contract_name CONTRACT_NAME The target contract name defined in the source code


User accounts
=============
You can specify what are the accounts used in the exploration.
Normaly you do not want the owner or deployer of the contract to send the symbolic transaction and to use a separate unused account to actually check the property methods.
There are 3 types of user accounts:

    - deployer:  The account used to create the target contract
    - senders: A set of accounts used to send symbolic transactions. Think that  these transactions are the ones trying to put the contract in a state that makes the property fail.
    - psender: The account used as caller to test the actual property methods


You can specify those via command line arguments ::

    --deployer DEPLOYER   (optional) address of account used to deploy the contract
    --senders SENDERS     (optional) a comma separated list of sender addresses.
                           The properties are going to be tested sending
                           transactions from these addresses.
    --psender PSENDER     (optional) address from where the property is tested


Or, if you prefer, you can specify a yaml file like this ::

    deployer: "0x41414141414141414141" 
    sender: ["0x51515151515151515151", "0x52525252525252525252"] 
    psender: "0x616161616161616161"

If you specify the accounts both ways the commandline takes precedence over the yaml file.
If you do not provide specific accounts **manticore-verifier** will choose them for you.


Stopping condition
==================
The exploration will continue to send symbolic transactions until one of the stopping criteria is met.

Maximum number of transactions
-----------------------------
You can be interested only in what could happen under a number of transactions. After a maximun number of transactions is reached the explorations ends. Properties that had not be found to be breakable are considered a pass.
You can modify the max number of transactions to test vis a command line argument, otherwise it will stop at 3 transactions. ::

     --maxt MAXT           Max transaction count to explore
 
Maximun coverage % attained
---------------------------
By default, if a transaction does not produce new coverage, the exploration is stopped. But you can add a further constraint so that if the provided coverage percentage is obtained, stop. Note that this is the total % of runtime bytecode covered. By default, compilers add dead code, and also in this case the runtime contains the code of the properties methods. So use with care. ::

     --maxcov MAXCOV       Stop after maxcov % coverage is obtained in the main
                            contract


Timeout
-------
Exploration will stop after the timeout seconds have pass. ::

     --timeout TIMEOUT     Exploration timeout in seconds


Walkthrough
-----------
Consider this little contract containing a bug:

.. code-block:: javascript

    contract Ownership{  // It can have an owner!
	    address owner = msg.sender;
	    function Onwer() public{
		    owner = msg.sender;
	    }
	    modifier isOwner(){
		    require(owner == msg.sender);
		    _;
	    }
    }
    contract Pausable is Ownership{ //It is also pausable. You can pause it. You can resume it.
        bool is_paused;
        modifier ifNotPaused(){
            require(!is_paused);
            _;
        }
        function paused() isOwner public{
            is_paused = true;
        }
        function resume() isOwner public{
            is_paused = false;
        }
    }
    contract Token is Pausable{ //<< HERE it is. 
        mapping(address => uint) public balances; // It maintains a balance sheet  
        function transfer(address to, uint value) ifNotPaused public{  //and can transfer value
            balances[msg.sender] -= value; // from one account
            balances[to] += value;         // to the other
        }
    }

Assuming the programmer did not want to allow the magic creation of tokens. 
We can design a property around the fact that the initial token count can not be increased over time. Even more relaxed, after the contract creation any account must have less that total count of tokens. The property looks like this :

.. code-block:: javascript

    contract TestToken is Token{
	    constructor() public{
		    //here lets initialize the thing
		    balances[msg.sender] = 10000; //deployer account owns it all!
	    }

	    function crytic_test_balance() view public returns (bool){
		    return balances[msg.sender] <= 10000; //nobody can have more than 100% of the tokens
	    }

    }

And you can unleash the verifier like this::

    $manticore-verifier testtoken.sol  --contract TestToken


f/
