contract AR {
    event Log(string);
    uint public a;
    uint public b;
    uint public c;

    function writea(uint wad) public {
        a=wad;
    }
    function writeb(uint wad) public {
        if (a==10){
            b=wad;
        }
    }
    function writec(uint wad) public {
        if (b==10){
            c=wad;
        }
    }
    function done() public {
        if (c==10){
            emit Log("Done!");
        }
    }
}
