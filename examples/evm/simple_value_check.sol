
contract Test {
    event Log(string);

    function target() payable public {
        if (msg.value > 10)
            emit Log("Value greater than 10");
        else
            emit Log("Value less or equal than 10");

    } 

}
