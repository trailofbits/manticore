#!/bin/bash

#This script pulls large files from Amazon S3

# this key only has access to the manticore-tests bucket, nothing else
export AWS_ACCESS_KEY_ID=AKIAIBSA5JBGMKCSIQWQ
export AWS_SECRET_ACCESS_KEY=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

echo "Copying files from S3..."
# this is the full dump list. Its big. You probably don't want all of them
# so its commented out by default
#CHROME47_DUMPS="00030100.dmp 01010300.dmp 02020e00.dmp 03040200.dmp 04030100.dmp 07040200.dmp 0a021400.dmp 0c030100.dmp 0d040200.dmp 0d050e00.dmp 0e011700.dmp 0f050200.dmp 11030100.dmp 11050e00.dmp 12011700.dmp 12040100.dmp 13001000.dmp 13001100.dmp 13050200.dmp 14001e00.dmp 16003d00.dmp 17001e00.dmp 17030100.dmp 18003d00.dmp 18011700.dmp 1a032900.dmp 1b001e00.dmp 1b004500.dmp 1b007200.dmp 1b030100.dmp 1c003d00.dmp 1e001e00.dmp 1f011700.dmp 1f040200.dmp 20003500.dmp 21006f00.dmp 22006800.dmp 22010300.dmp 23001e00.dmp 23004100.dmp 23040200.dmp 24003500.dmp 26001e00.dmp 27003d00.dmp 27006900.dmp 27030100.dmp 28003500.dmp 29001200.dmp 29006400.dmp 29040200.dmp 2a040100.dmp 2c030100.dmp 2e040200.dmp 2f001200.dmp 30006400.dmp 30011700.dmp 31020e00.dmp 33007100.dmp 33011700.dmp 34001200.dmp 34040200.dmp 35001f00.dmp 36005400.dmp 37006900.dmp 38007100.dmp 39001f00.dmp 39040200.dmp 3c005400.dmp 3c030100.dmp 3c050e00.dmp 3d002600.dmp 3e001200.dmp 3e021400.dmp 3f001300.dmp 41001f00.dmp 41006100.dmp 41006d00.dmp 42002600.dmp 43001300.dmp 44004b00.dmp 44022500.dmp 44030100.dmp 44040200.dmp 46040200.dmp 48004b00.dmp 49000900.dmp 49001300.dmp 49004300.dmp 49022500.dmp 49040100.dmp 4a000800.dmp 4a006d00.dmp 4a022900.dmp 4b001200.dmp 4b001b00.dmp 4b006100.dmp 4c030100.dmp 4c040100.dmp 4f001f00.dmp 50001200.dmp 50004b00.dmp 50007100.dmp 50022900.dmp 50040100.dmp 51001300.dmp 52006d00.dmp 54030100.dmp 55004b00.dmp 55030e00.dmp 56012500.dmp 56022900.dmp 58001300.dmp 58001f00.dmp 5a006100.dmp 5b004b00.dmp 5b006d00.dmp 5c001900.dmp 5c040200.dmp 5d001300.dmp 5d022900.dmp 5e000800.dmp 61001900.dmp 61030100.dmp 63004b00.dmp 63022900.dmp 64002a00.dmp 65030100.dmp 66003700.dmp 66003c00.dmp 67001900.dmp 68001b00.dmp 68001f00.dmp 68040200.dmp 69004b00.dmp 69012500.dmp 6b002e00.dmp 6c005200.dmp 6d001b00.dmp 6d001f00.dmp 6d002300.dmp 6e040200.dmp 6f000900.dmp 6f011a00.dmp 6f040100.dmp 71022900.dmp 72000900.dmp 72003700.dmp 73002300.dmp 73002a00.dmp 73011a00.dmp 74001900.dmp 75001b00.dmp 75002e00.dmp 76000800.dmp 76010c00.dmp 77001900.dmp 78002800.dmp 78003700.dmp 78011a00.dmp 79000900.dmp 7b002a00.dmp 7c022900.dmp 7c030100.dmp 7d002e00.dmp 7e011a00.dmp 7e040100.dmp 80001b00.dmp 80002300.dmp 82002e00.dmp 82004300.dmp 83011a00.dmp 87001b00.dmp 87011a00.dmp 87022900.dmp 87040100.dmp 87040200.dmp 88002300.dmp 8b004300.dmp 8c002300.dmp 8c011a00.dmp 8d001c00.dmp 8e040200.dmp 90011a00.dmp 96011a00.dmp 98001c00.dmp 9a003700.dmp 9b022900.dmp 9e003700.dmp 9e040200.dmp a1004300.dmp a1022900.dmp a3003700.dmp a4040100.dmp a7040200.dmp ab040200.dmp ac030100.dmp b0040200.dmp b4022900.dmp bb020100.dmp bc001c00.dmp bc004a00.dmp c0001c00.dmp c0004a00.dmp c0012500.dmp c6020100.dmp ca020100.dmp cc030100.dmp cd040200.dmp d0030200.dmp d3020100.dmp d3030100.dmp d4022900.dmp d7020100.dmp d8022900.dmp d8030200.dmp db020100.dmp dc001c00.dmp dd011400.dmp e1001c00.dmp e1011400.dmp e1020100.dmp e1040200.dmp e2001700.dmp e2030200.dmp e4020100.dmp e7030200.dmp e7040200.dmp e8001700.dmp e8011400.dmp e9022900.dmp eb040200.dmp ed001700.dmp ed022900.dmp f1002d00.dmp f2011400.dmp f2022900.dmp f3020100.dmp f4001700.dmp f4040200.dmp f5030200.dmp f6011400.dmp f6020100.dmp f7022900.dmp f8002d00.dmp f9001700.dmp f9030200.dmp fa011400.dmp fc022900.dmp fc030100.dmp fd020100.dmp fe011400.dmp ff030100.dmp ffff0000.dmp"

CHROME47_DUMPS="00030100.dmp  29006400.dmp ffff0000.dmp"
for dmp in ${CHROME47_DUMPS}
do
    aws s3 cp s3://manticore-tests/chrome47/${dmp} chrome47/ --region us-east-1
done

CHROME49_DUMPS="10c8_mojo.dmp 1518_mojo.dmp 80_mojo.dmp 88_mojo.dmp"
for dmp in ${CHROME49_DUMPS}
do
    aws s3 cp s3://manticore-tests/chrome49/${dmp} chrome49/ --region us-east-1
done

echo "All Done"
