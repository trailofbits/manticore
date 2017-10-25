/* There is two main functions `explore` and  `explore2`
`explore` is the first level of exploration, you have to call it multiple times to explore the path
`explore2` is a bit more complex, the owner has to call first the `enable_exploration` function
*/
pragma solidity ^0.4.15;

contract Coverage{
    address private owner;

    // only used for more complex exploration
    bool private exploration = false; 

    mapping(address => uint) private balances;

    event Give(address, address, uint);
    event Take(address, address, uint);

    modifier onlyowner {
        require(msg.sender==owner);
        _;
    }

    modifier onlyExplorationOn{
        require(exploration);
        _;
    }

    function Coverage()
        public 
    {
        owner = msg.sender;
    }
    
    function enable_exploration() 
        public 
        onlyowner
    {
        exploration = true;
    }

    function balanceOf(address user) 
        returns (uint)
    {
        return balances[user];
    }

    function add(address user, uint val)
        private
    {
        // comment the require to trigger overflow
        require(balances[user] + val >= val);
        balances[user] += val;
    }

    function remove(address user, uint val)
        private
    {
        // comment the require to trigger underflow
        require(balances[user] >= val);
        balances[user] -= val;
    }

    // Entry point for simple exploration
    // Anyone can give or take to anyone
    // But if you cant take to someone poorer than you
    function explore(uint value, address user, bool give)
        public
    {
        // do not play if you are empty
        if(balances[msg.sender] == 0){
            balances[msg.sender] = 42;
            return;
        }
        if(give){
            remove(msg.sender, value);
            add(user, value);
            Give(msg.sender, user, value);
        }
        else{
            if( balances[user] > balances[msg.sender]){
                uint diff;
                // only keep the minimum that can be taken
                diff  = balances[user] - balances[msg.sender];
                value = diff >value ? value : diff;
                add(msg.sender, value);
                remove(user, value);
                Take(msg.sender, user, value);
            }
            else{
                // If you try to take to someone poorer than you
                // you will give it the value
                remove(msg.sender, value);
                add(user, value);
                Give(msg.sender, user, value);
            }
        }
    }

    // Same as explore, but you can really take to anyone
    function explore2(uint value, address user, bool give)
        onlyExplorationOn
        public
    {
        if(give){
            remove(msg.sender, value);
            add(user, value);
            Give(msg.sender, user, value);
        }
        else{
            uint diff;
            // only keep the minimum that can be taken
            diff  = balances[user] - balances[msg.sender];
            value = diff >value ? value : diff;
            add(msg.sender, value);
            remove(user, value);
            Take(msg.sender, user, value);
        }
    }
}

