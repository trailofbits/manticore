pragma solidity ^0.4.24;
/*
   Example contract - True Negative
   The return value of a low level call IS checked via solidity injected code.
   This should NOT report a finding.
*/
contract DetectThis {
  uint secret = 0;

  function callchecked() public returns (uint256){
    uint old_secret = secret;
    uint current_block_timestamp = now;
    uint current_block_coinbase = uint(block.coinbase);
    uint current_block_difficulty = block.difficulty;
    uint current_block_number = block.number;
    uint current_block_blockhash = uint(blockhash(block.number-1));
    uint tx_origin = uint(tx.origin);
    uint tx_gasprice =  tx.gasprice;
    uint current_block_gaslimit = block.gaslimit;
    secret = current_block_timestamp ^ current_block_coinbase ^ current_block_difficulty ^ current_block_number ^ current_block_blockhash ^ tx_origin ^ tx_gasprice ^ current_block_gaslimit;
    return old_secret;
  }

}
