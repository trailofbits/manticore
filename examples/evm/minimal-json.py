from manticore.ethereum import ManticoreEVM

################ Script #######################

m = ManticoreEVM()

# And now make the contract account to analyze
truffle_json = r"""{
  "contractName": "MetaCoin",
  "abi": [
    {
      "inputs": [
        {
          "name": "addr",
          "type": "address"
        }
      ],
      "name": "getBalanceInEth",
      "outputs": [
        {
          "name": "",
          "type": "uint256"
        }
      ],
      "stateMutability": "nonpayable",
      "type": "function"
    },
    {
      "inputs": [
        {
          "name": "receiver",
          "type": "address"
        },
        {
          "name": "amount",
          "type": "uint256"
        }
      ],
      "name": "sendCoin",
      "outputs": [
        {
          "name": "sufficient",
          "type": "bool"
        }
      ],
      "stateMutability": "nonpayable",
      "type": "function"
    },
    {
      "inputs": [
        {
          "name": "addr",
          "type": "address"
        }
      ],
      "name": "getBalance",
      "outputs": [
        {
          "name": "",
          "type": "uint256"
        }
      ],
      "stateMutability": "nonpayable",
      "type": "function"
    },
    {
      "inputs": [],
      "stateMutability": "nonpayable",
      "type": "constructor"
    },
    {
      "anonymous": false,
      "inputs": [
        {
          "indexed": true,
          "name": "_from",
          "type": "address"
        },
        {
          "indexed": true,
          "name": "_to",
          "type": "address"
        },
        {
          "indexed": false,
          "name": "_value",
          "type": "uint256"
        }
      ],
      "name": "Transfer",
      "type": "event"
    }
  ],
  "bytecode": "0x6060604052341561000c57fe5b5b600160a060020a033216600090815260208190526040902061271090555b5b6102308061003b6000396000f300606060405263ffffffff60e060020a6000350416637bd703e8811461003757806390b98a1114610065578063f8b2cb4f14610098575bfe5b341561003f57fe5b610053600160a060020a03600435166100c6565b60408051918252519081900360200190f35b341561006d57fe5b610084600160a060020a036004351660243561014d565b604080519115158252519081900360200190f35b34156100a057fe5b610053600160a060020a03600435166101e5565b60408051918252519081900360200190f35b600073__ConvertLib____________________________6396e4ee3d6100eb846101e5565b60026000604051602001526040518363ffffffff1660e060020a028152600401808381526020018281526020019250505060206040518083038186803b151561013057fe5b6102c65a03f4151561013e57fe5b5050604051519150505b919050565b600160a060020a03331660009081526020819052604081205482901015610176575060006101df565b600160a060020a0333811660008181526020818152604080832080548890039055938716808352918490208054870190558351868152935191937fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef929081900390910190a35060015b92915050565b600160a060020a0381166000908152602081905260409020545b9190505600a165627a7a72305820f596963383bc39946413f0f0b34aee51796e6ae4b1b68b334f880b30a36ec6730029",
  "deployedBytecode": "0x606060405263ffffffff60e060020a6000350416637bd703e8811461003757806390b98a1114610065578063f8b2cb4f14610098575bfe5b341561003f57fe5b610053600160a060020a03600435166100c6565b60408051918252519081900360200190f35b341561006d57fe5b610084600160a060020a036004351660243561014d565b604080519115158252519081900360200190f35b34156100a057fe5b610053600160a060020a03600435166101e5565b60408051918252519081900360200190f35b600073__ConvertLib____________________________6396e4ee3d6100eb846101e5565b60026000604051602001526040518363ffffffff1660e060020a028152600401808381526020018281526020019250505060206040518083038186803b151561013057fe5b6102c65a03f4151561013e57fe5b5050604051519150505b919050565b600160a060020a03331660009081526020819052604081205482901015610176575060006101df565b600160a060020a0333811660008181526020818152604080832080548890039055938716808352918490208054870190558351868152935191937fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef929081900390910190a35060015b92915050565b600160a060020a0381166000908152602081905260409020545b9190505600a165627a7a72305820f596963383bc39946413f0f0b34aee51796e6ae4b1b68b334f880b30a36ec6730029",
  "sourceMap": "315:637:1:-;;;452:55;;;;;;;-1:-1:-1;;;;;485:9:1;476:19;:8;:19;;;;;;;;;;498:5;476:27;;452:55;315:637;;;;;;;",
  "source": "pragma solidity ^0.4.4;\n\nimport \"./ConvertLib.sol\";\n\n// This is just a simple example of a coin-like contract.\n// It is not standards compatible and cannot be expected to talk to other\n// coin/token contracts. If you want to create a standards-compliant\n// token, see: https://github.com/ConsenSys/Tokens. Cheers!\n\ncontract MetaCoin {\n\tmapping (address => uint) balances;\n\n\tevent Transfer(address indexed _from, address indexed _to, uint256 _value);\n\n\tfunction MetaCoin() {\n\t\tbalances[tx.origin] = 10000;\n\t}\n\n\tfunction sendCoin(address receiver, uint amount) returns(bool sufficient) {\n\t\tif (balances[msg.sender] < amount) return false;\n\t\tbalances[msg.sender] -= amount;\n\t\tbalances[receiver] += amount;\n\t\tTransfer(msg.sender, receiver, amount);\n\t\treturn true;\n\t}\n\n\tfunction getBalanceInEth(address addr) returns(uint){\n\t\treturn ConvertLib.convert(getBalance(addr),2);\n\t}\n\n\tfunction getBalance(address addr) returns(uint) {\n\t\treturn balances[addr];\n\t}\n}\n",
  "sourcePath": "/Users/gnidan/tmp/metacoin/contracts/MetaCoin.sol",
  "ast": {
    "children": [
      {
        "attributes": {
          "literals": [
            "solidity",
            "^",
            "0.4",
            ".4"
          ]
        },
        "id": 18,
        "name": "PragmaDirective",
        "src": "0:23:1"
      },
      {
        "attributes": {
          "file": "./ConvertLib.sol"
        },
        "id": 19,
        "name": "ImportDirective",
        "src": "25:26:1"
      },
      {
        "attributes": {
          "fullyImplemented": true,
          "isLibrary": false,
          "linearizedBaseContracts": [
            112
          ],
          "name": "MetaCoin"
        },
        "children": [
          {
            "attributes": {
              "constant": false,
              "name": "balances",
              "storageLocation": "default",
              "type": "mapping(address => uint256)",
              "visibility": "internal"
            },
            "children": [
              {
                "children": [
                  {
                    "attributes": {
                      "name": "address"
                    },
                    "id": 20,
                    "name": "ElementaryTypeName",
                    "src": "345:7:1"
                  },
                  {
                    "attributes": {
                      "name": "uint"
                    },
                    "id": 21,
                    "name": "ElementaryTypeName",
                    "src": "356:4:1"
                  }
                ],
                "id": 22,
                "name": "Mapping",
                "src": "336:25:1"
              }
            ],
            "id": 23,
            "name": "VariableDeclaration",
            "src": "336:34:1"
          },
          {
            "attributes": {
              "name": "Transfer"
            },
            "children": [
              {
                "children": [
                  {
                    "attributes": {
                      "constant": false,
                      "indexed": true,
                      "name": "_from",
                      "storageLocation": "default",
                      "type": "address",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "address"
                        },
                        "id": 24,
                        "name": "ElementaryTypeName",
                        "src": "389:7:1"
                      }
                    ],
                    "id": 25,
                    "name": "VariableDeclaration",
                    "src": "389:21:1"
                  },
                  {
                    "attributes": {
                      "constant": false,
                      "indexed": true,
                      "name": "_to",
                      "storageLocation": "default",
                      "type": "address",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "address"
                        },
                        "id": 26,
                        "name": "ElementaryTypeName",
                        "src": "412:7:1"
                      }
                    ],
                    "id": 27,
                    "name": "VariableDeclaration",
                    "src": "412:19:1"
                  },
                  {
                    "attributes": {
                      "constant": false,
                      "indexed": false,
                      "name": "_value",
                      "storageLocation": "default",
                      "type": "uint256",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "uint256"
                        },
                        "id": 28,
                        "name": "ElementaryTypeName",
                        "src": "433:7:1"
                      }
                    ],
                    "id": 29,
                    "name": "VariableDeclaration",
                    "src": "433:14:1"
                  }
                ],
                "id": 30,
                "name": "ParameterList",
                "src": "388:60:1"
              }
            ],
            "id": 31,
            "name": "EventDefinition",
            "src": "374:75:1"
          },
          {
            "attributes": {
              "constant": false,
              "name": "MetaCoin",
              "payable": false,
              "visibility": "public"
            },
            "children": [
              {
                "children": [],
                "id": 32,
                "name": "ParameterList",
                "src": "469:2:1"
              },
              {
                "children": [],
                "id": 33,
                "name": "ParameterList",
                "src": "472:0:1"
              },
              {
                "children": [
                  {
                    "children": [
                      {
                        "attributes": {
                          "operator": "=",
                          "type": "uint256"
                        },
                        "children": [
                          {
                            "attributes": {
                              "type": "uint256"
                            },
                            "children": [
                              {
                                "attributes": {
                                  "type": "mapping(address => uint256)",
                                  "value": "balances"
                                },
                                "id": 34,
                                "name": "Identifier",
                                "src": "476:8:1"
                              },
                              {
                                "attributes": {
                                  "member_name": "origin",
                                  "type": "address"
                                },
                                "children": [
                                  {
                                    "attributes": {
                                      "type": "tx",
                                      "value": "tx"
                                    },
                                    "id": 35,
                                    "name": "Identifier",
                                    "src": "485:2:1"
                                  }
                                ],
                                "id": 36,
                                "name": "MemberAccess",
                                "src": "485:9:1"
                              }
                            ],
                            "id": 37,
                            "name": "IndexAccess",
                            "src": "476:19:1"
                          },
                          {
                            "attributes": {
                              "hexvalue": "3130303030",
                              "subdenomination": null,
                              "token": null,
                              "type": "int_const 10000",
                              "value": "10000"
                            },
                            "id": 38,
                            "name": "Literal",
                            "src": "498:5:1"
                          }
                        ],
                        "id": 39,
                        "name": "Assignment",
                        "src": "476:27:1"
                      }
                    ],
                    "id": 40,
                    "name": "ExpressionStatement",
                    "src": "476:27:1"
                  }
                ],
                "id": 41,
                "name": "Block",
                "src": "472:35:1"
              }
            ],
            "id": 42,
            "name": "FunctionDefinition",
            "src": "452:55:1"
          },
          {
            "attributes": {
              "constant": false,
              "name": "sendCoin",
              "payable": false,
              "visibility": "public"
            },
            "children": [
              {
                "children": [
                  {
                    "attributes": {
                      "constant": false,
                      "name": "receiver",
                      "storageLocation": "default",
                      "type": "address",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "address"
                        },
                        "id": 43,
                        "name": "ElementaryTypeName",
                        "src": "528:7:1"
                      }
                    ],
                    "id": 44,
                    "name": "VariableDeclaration",
                    "src": "528:16:1"
                  },
                  {
                    "attributes": {
                      "constant": false,
                      "name": "amount",
                      "storageLocation": "default",
                      "type": "uint256",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "uint"
                        },
                        "id": 45,
                        "name": "ElementaryTypeName",
                        "src": "546:4:1"
                      }
                    ],
                    "id": 46,
                    "name": "VariableDeclaration",
                    "src": "546:11:1"
                  }
                ],
                "id": 47,
                "name": "ParameterList",
                "src": "527:31:1"
              },
              {
                "children": [
                  {
                    "attributes": {
                      "constant": false,
                      "name": "sufficient",
                      "storageLocation": "default",
                      "type": "bool",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "bool"
                        },
                        "id": 48,
                        "name": "ElementaryTypeName",
                        "src": "567:4:1"
                      }
                    ],
                    "id": 49,
                    "name": "VariableDeclaration",
                    "src": "567:15:1"
                  }
                ],
                "id": 50,
                "name": "ParameterList",
                "src": "566:17:1"
              },
              {
                "children": [
                  {
                    "children": [
                      {
                        "attributes": {
                          "operator": "<",
                          "type": "bool"
                        },
                        "children": [
                          {
                            "attributes": {
                              "type": "uint256"
                            },
                            "children": [
                              {
                                "attributes": {
                                  "type": "mapping(address => uint256)",
                                  "value": "balances"
                                },
                                "id": 51,
                                "name": "Identifier",
                                "src": "592:8:1"
                              },
                              {
                                "attributes": {
                                  "member_name": "sender",
                                  "type": "address"
                                },
                                "children": [
                                  {
                                    "attributes": {
                                      "type": "msg",
                                      "value": "msg"
                                    },
                                    "id": 52,
                                    "name": "Identifier",
                                    "src": "601:3:1"
                                  }
                                ],
                                "id": 53,
                                "name": "MemberAccess",
                                "src": "601:10:1"
                              }
                            ],
                            "id": 54,
                            "name": "IndexAccess",
                            "src": "592:20:1"
                          },
                          {
                            "attributes": {
                              "type": "uint256",
                              "value": "amount"
                            },
                            "id": 55,
                            "name": "Identifier",
                            "src": "615:6:1"
                          }
                        ],
                        "id": 56,
                        "name": "BinaryOperation",
                        "src": "592:29:1"
                      },
                      {
                        "children": [
                          {
                            "attributes": {
                              "hexvalue": "66616c7365",
                              "subdenomination": null,
                              "token": "false",
                              "type": "bool",
                              "value": "false"
                            },
                            "id": 57,
                            "name": "Literal",
                            "src": "630:5:1"
                          }
                        ],
                        "id": 58,
                        "name": "Return",
                        "src": "623:12:1"
                      }
                    ],
                    "id": 59,
                    "name": "IfStatement",
                    "src": "588:47:1"
                  },
                  {
                    "children": [
                      {
                        "attributes": {
                          "operator": "-=",
                          "type": "uint256"
                        },
                        "children": [
                          {
                            "attributes": {
                              "type": "uint256"
                            },
                            "children": [
                              {
                                "attributes": {
                                  "type": "mapping(address => uint256)",
                                  "value": "balances"
                                },
                                "id": 60,
                                "name": "Identifier",
                                "src": "639:8:1"
                              },
                              {
                                "attributes": {
                                  "member_name": "sender",
                                  "type": "address"
                                },
                                "children": [
                                  {
                                    "attributes": {
                                      "type": "msg",
                                      "value": "msg"
                                    },
                                    "id": 61,
                                    "name": "Identifier",
                                    "src": "648:3:1"
                                  }
                                ],
                                "id": 62,
                                "name": "MemberAccess",
                                "src": "648:10:1"
                              }
                            ],
                            "id": 63,
                            "name": "IndexAccess",
                            "src": "639:20:1"
                          },
                          {
                            "attributes": {
                              "type": "uint256",
                              "value": "amount"
                            },
                            "id": 64,
                            "name": "Identifier",
                            "src": "663:6:1"
                          }
                        ],
                        "id": 65,
                        "name": "Assignment",
                        "src": "639:30:1"
                      }
                    ],
                    "id": 66,
                    "name": "ExpressionStatement",
                    "src": "639:30:1"
                  },
                  {
                    "children": [
                      {
                        "attributes": {
                          "operator": "+=",
                          "type": "uint256"
                        },
                        "children": [
                          {
                            "attributes": {
                              "type": "uint256"
                            },
                            "children": [
                              {
                                "attributes": {
                                  "type": "mapping(address => uint256)",
                                  "value": "balances"
                                },
                                "id": 67,
                                "name": "Identifier",
                                "src": "673:8:1"
                              },
                              {
                                "attributes": {
                                  "type": "address",
                                  "value": "receiver"
                                },
                                "id": 68,
                                "name": "Identifier",
                                "src": "682:8:1"
                              }
                            ],
                            "id": 69,
                            "name": "IndexAccess",
                            "src": "673:18:1"
                          },
                          {
                            "attributes": {
                              "type": "uint256",
                              "value": "amount"
                            },
                            "id": 70,
                            "name": "Identifier",
                            "src": "695:6:1"
                          }
                        ],
                        "id": 71,
                        "name": "Assignment",
                        "src": "673:28:1"
                      }
                    ],
                    "id": 72,
                    "name": "ExpressionStatement",
                    "src": "673:28:1"
                  },
                  {
                    "children": [
                      {
                        "attributes": {
                          "type": "tuple()",
                          "type_conversion": false
                        },
                        "children": [
                          {
                            "attributes": {
                              "type": "function (address,address,uint256) constant",
                              "value": "Transfer"
                            },
                            "id": 73,
                            "name": "Identifier",
                            "src": "705:8:1"
                          },
                          {
                            "attributes": {
                              "member_name": "sender",
                              "type": "address"
                            },
                            "children": [
                              {
                                "attributes": {
                                  "type": "msg",
                                  "value": "msg"
                                },
                                "id": 74,
                                "name": "Identifier",
                                "src": "714:3:1"
                              }
                            ],
                            "id": 75,
                            "name": "MemberAccess",
                            "src": "714:10:1"
                          },
                          {
                            "attributes": {
                              "type": "address",
                              "value": "receiver"
                            },
                            "id": 76,
                            "name": "Identifier",
                            "src": "726:8:1"
                          },
                          {
                            "attributes": {
                              "type": "uint256",
                              "value": "amount"
                            },
                            "id": 77,
                            "name": "Identifier",
                            "src": "736:6:1"
                          }
                        ],
                        "id": 78,
                        "name": "FunctionCall",
                        "src": "705:38:1"
                      }
                    ],
                    "id": 79,
                    "name": "ExpressionStatement",
                    "src": "705:38:1"
                  },
                  {
                    "children": [
                      {
                        "attributes": {
                          "hexvalue": "74727565",
                          "subdenomination": null,
                          "token": "true",
                          "type": "bool",
                          "value": "true"
                        },
                        "id": 80,
                        "name": "Literal",
                        "src": "754:4:1"
                      }
                    ],
                    "id": 81,
                    "name": "Return",
                    "src": "747:11:1"
                  }
                ],
                "id": 82,
                "name": "Block",
                "src": "584:178:1"
              }
            ],
            "id": 83,
            "name": "FunctionDefinition",
            "src": "510:252:1"
          },
          {
            "attributes": {
              "constant": false,
              "name": "getBalanceInEth",
              "payable": false,
              "visibility": "public"
            },
            "children": [
              {
                "children": [
                  {
                    "attributes": {
                      "constant": false,
                      "name": "addr",
                      "storageLocation": "default",
                      "type": "address",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "address"
                        },
                        "id": 84,
                        "name": "ElementaryTypeName",
                        "src": "790:7:1"
                      }
                    ],
                    "id": 85,
                    "name": "VariableDeclaration",
                    "src": "790:12:1"
                  }
                ],
                "id": 86,
                "name": "ParameterList",
                "src": "789:14:1"
              },
              {
                "children": [
                  {
                    "attributes": {
                      "constant": false,
                      "name": "",
                      "storageLocation": "default",
                      "type": "uint256",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "uint"
                        },
                        "id": 87,
                        "name": "ElementaryTypeName",
                        "src": "812:4:1"
                      }
                    ],
                    "id": 88,
                    "name": "VariableDeclaration",
                    "src": "812:4:1"
                  }
                ],
                "id": 89,
                "name": "ParameterList",
                "src": "811:6:1"
              },
              {
                "children": [
                  {
                    "children": [
                      {
                        "attributes": {
                          "type": "uint256",
                          "type_conversion": false
                        },
                        "children": [
                          {
                            "attributes": {
                              "member_name": "convert",
                              "type": "function (uint256,uint256) returns (uint256)"
                            },
                            "children": [
                              {
                                "attributes": {
                                  "type": "type(library ConvertLib)",
                                  "value": "ConvertLib"
                                },
                                "id": 90,
                                "name": "Identifier",
                                "src": "828:10:1"
                              }
                            ],
                            "id": 91,
                            "name": "MemberAccess",
                            "src": "828:18:1"
                          },
                          {
                            "attributes": {
                              "type": "uint256",
                              "type_conversion": false
                            },
                            "children": [
                              {
                                "attributes": {
                                  "type": "function (address) returns (uint256)",
                                  "value": "getBalance"
                                },
                                "id": 92,
                                "name": "Identifier",
                                "src": "847:10:1"
                              },
                              {
                                "attributes": {
                                  "type": "address",
                                  "value": "addr"
                                },
                                "id": 93,
                                "name": "Identifier",
                                "src": "858:4:1"
                              }
                            ],
                            "id": 94,
                            "name": "FunctionCall",
                            "src": "847:16:1"
                          },
                          {
                            "attributes": {
                              "hexvalue": "32",
                              "subdenomination": null,
                              "token": null,
                              "type": "int_const 2",
                              "value": "2"
                            },
                            "id": 95,
                            "name": "Literal",
                            "src": "864:1:1"
                          }
                        ],
                        "id": 96,
                        "name": "FunctionCall",
                        "src": "828:38:1"
                      }
                    ],
                    "id": 97,
                    "name": "Return",
                    "src": "821:45:1"
                  }
                ],
                "id": 98,
                "name": "Block",
                "src": "817:53:1"
              }
            ],
            "id": 99,
            "name": "FunctionDefinition",
            "src": "765:105:1"
          },
          {
            "attributes": {
              "constant": false,
              "name": "getBalance",
              "payable": false,
              "visibility": "public"
            },
            "children": [
              {
                "children": [
                  {
                    "attributes": {
                      "constant": false,
                      "name": "addr",
                      "storageLocation": "default",
                      "type": "address",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "address"
                        },
                        "id": 100,
                        "name": "ElementaryTypeName",
                        "src": "893:7:1"
                      }
                    ],
                    "id": 101,
                    "name": "VariableDeclaration",
                    "src": "893:12:1"
                  }
                ],
                "id": 102,
                "name": "ParameterList",
                "src": "892:14:1"
              },
              {
                "children": [
                  {
                    "attributes": {
                      "constant": false,
                      "name": "",
                      "storageLocation": "default",
                      "type": "uint256",
                      "visibility": "internal"
                    },
                    "children": [
                      {
                        "attributes": {
                          "name": "uint"
                        },
                        "id": 103,
                        "name": "ElementaryTypeName",
                        "src": "915:4:1"
                      }
                    ],
                    "id": 104,
                    "name": "VariableDeclaration",
                    "src": "915:4:1"
                  }
                ],
                "id": 105,
                "name": "ParameterList",
                "src": "914:6:1"
              },
              {
                "children": [
                  {
                    "children": [
                      {
                        "attributes": {
                          "type": "uint256"
                        },
                        "children": [
                          {
                            "attributes": {
                              "type": "mapping(address => uint256)",
                              "value": "balances"
                            },
                            "id": 106,
                            "name": "Identifier",
                            "src": "932:8:1"
                          },
                          {
                            "attributes": {
                              "type": "address",
                              "value": "addr"
                            },
                            "id": 107,
                            "name": "Identifier",
                            "src": "941:4:1"
                          }
                        ],
                        "id": 108,
                        "name": "IndexAccess",
                        "src": "932:14:1"
                      }
                    ],
                    "id": 109,
                    "name": "Return",
                    "src": "925:21:1"
                  }
                ],
                "id": 110,
                "name": "Block",
                "src": "921:29:1"
              }
            ],
            "id": 111,
            "name": "FunctionDefinition",
            "src": "873:77:1"
          }
        ],
        "id": 112,
        "name": "ContractDefinition",
        "src": "315:637:1"
      }
    ],
    "name": "SourceUnit"
  },
  "networks": {
    "1494889277189": {
      "address": "0x657b316c4c7df70999a69c2475e59152f87a04aa",
      "links": {
        "ConvertLib": {
          "address": "0x7bcc63d45790e23f6e9bc3514e1ab5af649302d0",
          "events": {
            "0xa163a6249e860c278ef4049759a7f7c7e8c141d30fd634fda9b5a6a95d111a30": {
              "anonymous": false,
              "inputs": [],
              "name": "Test",
              "type": "event"
            }
          }
        }
      }
    }
  },
  "updatedAt": "2017-05-15T20:46:00Z",
  "schemaVersion": "0.0.5"
}
"""

user_account = m.create_account(balance=1000, name="user_account")
print("[+] Creating a user account", user_account.name_)

contract_account = m.solidity_create_contract(
    truffle_json, owner=user_account, name="contract_account"
)
print("[+] Creating a contract account", contract_account.name_)
contract_account.sendCoin(1, 1)

print("[+] Now the symbolic values")
symbolic_data = m.make_symbolic_buffer(320)
symbolic_value = m.make_symbolic_value(name="VALUE")
symbolic_address = m.make_symbolic_value(name="ADDRESS")
symbolic_caller = m.make_symbolic_value(name="CALLER")
m.transaction(
    caller=symbolic_caller, address=symbolic_address, data=symbolic_data, value=symbolic_value
)

# Let seth know we are not sending more transactions
m.finalize()
print(f"[+] Look for results in {m.workspace}")
