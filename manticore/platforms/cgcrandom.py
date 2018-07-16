from binascii import unhexlify
#./print_random seed=0000000000000000000000000000000000000000000000000000000000000000000000000000000000
seed = '0000000000000000000000000000000000000000000000000000000000000000000000000000000000'
stream = 'f795bd4a52e29ed713d313fa20e98dbcc8d1e5115952f7fa3738b4c5ceb2b09a0d9cc50d16e1bcedcf6062099d20837e6f39e0cb767c0debffa00e54'
stream += 'e89ba679f60865f512d37070e748b00ea5a090cbe226cbffd135f48cee4e1ae66923369a97729ba14591a4908ae16fb07a3226bafa494f2501e95dee'
stream += 'd7149ad824c0f2d5cc23f0059dc83fc17efbb4409773bfaed54d441d46768ed7ed878408f8de121ed411a6dfa262c78d37f7366e1803a4c56e1e0b76'
stream += 'b815690de5f9908eeae544e7988698cbebdf49da51c9d88a729cfc40a2dfe92037a6c1c5f9a8b72642a5c725f94415a153ba4f036899c78fd1fcf093'
stream += '8b2536004aaeaf6e626ee160770f3051fb3b574a094b620c0fa4804afef448ec9437b8a6faf9da30908a7bd0d5606d832e5dd0ec810578aa598e9914'
stream += '3b965f1e0b9715c49d0fe0f691a7106eaba43bfd1c185678b407300f85c28d609c1987d1f5d23968be55982f5ea3eb8f2370a8040edd6a385b98f6f6'
stream += 'f28b271533cab1eb1653a4b8023c323282299b445a8fca5aed2b2cc6a0740dee3dc6bf5171a317a392f87dae4a1cbe54cfa6c4c1794464c589f51daa'
stream += '8fa81d17b04811ce430088f790502e091d022994317674358bbae64a347d7e621802abdbe6a1ea80f1dc2f1d3dd1124448ac7d14aa11a235b1e2cb44'
stream += 'f50a8e379e015c3495496f2488da8b4aefb46f67672c46a86c7d4e45855eaa7daaa63ceb17452f433deb144def280c82cf5d3ac2d1cc02d56a8a0916'
stream += '321b1606eca356d472cece5b95699af02e6266ee61f3c51ab3817db1043bd8d8ff4b34c36ee2da1faf97c97bcfa967fbe72e363533baa28da46f9cb6'
stream += '87cab374957e45d46561aa803c70119ebdc7d3e5ec4a4d771ceea8b933d4c3e2616c38e83a215dca5767c9eabcc2a5622957c6c785a1890415057680'
stream += '932a46e439e3ce44b09f700f8fac58c422e865ed519725da7c475454617dbb5678dfcaa6d093aa133ff2e4a74163ce1b1cb3d99dbe445f39b997249c'
stream += 'ec5f3fb17923a310eb1e62cbb93d3a3e84f3d20169483514baed671567467749f886b89a75c2c6291b85139dc4f95046a3e1ee94d015c6d73ed548c3'
stream += 'b48131f6e0660b646cb2fb07db0284f41ebf66068f98fd5508ee57df4626297ad60b4bafef0e25958e223866efab0e7e12fe9acb66dcc3cb002bd967'
stream += '517f5c4a632828290300ceaaf116e35025953c4c7c8ccd60587ab9c914184a701f81fa21c403b2a69b0c935d5e9a62b986fbb6a3417ee94f2ebe9959'
stream += '5a90b5637952a4408c190d77afdc581650661c00390b029d0801e4f616696cbcf9d91d67a147fcfd465a117ac2f9208fd98942d4602548bab0a2ceea'
stream += 'd333d0ce7daf8451f8d5812bb54000a0e0e1a939ad6384d5b9a8fe84c214208df0723bc68a72f88558cd7e0b6c47fdc10a2b46e77a7b6d65ed4e9bb2'
stream += '93862570234aadd3aebecc4c1faa63e3819d114e67c8aaf5d3e0c286a287e616b9d156e965937f61aa5f6b64de1f98198aec6478e56c72f881c2052f'
stream += '7a42f30f281dbec3474f1095cf27308a44a1e80cab0469735fa26dfa923229c89b6b7da47ecc051cc87767455e886ffdd6ce9271923a5a198d79de6b'
stream += '1ac0f863434a9815ea8b8efa7102f86bca7774d528621bb2e4cb2ff93a43c8cbe15c6d9018097a0eb042e62ff0fbc7123dfbadb72fcd9a13a57bb0ae'
stream += 'b91bba5cf321b5b619ad530f26524455b5855b2094c3f860b9766a2f0fa1830920ac1e483fe8f564438fb9e271d98a3890a862fecfd06e32dba264ce'
stream += '0afc5f0aee6468a41c28d3321cb09f0819617ab9a5ef8f9a461ffe708467dec83885112d92d59fb1f8a2815dc790a338db4bbca3d673b2390842a637'
stream += 'f9b52023681931951b09d9c7c9c904be43e103e80ad78f0518e7a393823796d9b33a6480fd77c66947d1b6caad2030949fd7b6cb5b6407dfcb81386f'
stream += '0043a489b2946b5d05ec041b26cdea54e8db3cc2c84fe193d98cb85b96bb57d42cb5a39bd66c69aea2343d648c360f7877b6c8c55fd4322f401eea08'
stream += '796a58b8e30727a660fc23669f2b31bf242d11af106c64716c7a76596d2c4e02bc71d9c75ed4d6e5861396282d2cbe0c30ff306e4a129f89a2ad2c7e'
stream += 'e78b2bf091a4eb1569ccfae7e0248e2f594c5138d8d925048da3392c0450063d21aa400ade9c8be384699a1f315de8d4e57de38d698bbb3d6d7012ed'
stream += '5c6b75b96bd1923203f1726091182001ba92270bb6d0e7d0822382018baff5d14c1dfc477d7142942c346b384e8b008cef49bc86ec9aa4275ac5bf3e'
stream += '1e707b18b058fb4cf39e97cf443468f41ea45ef1bbbe412c63952dd60ac06f50b0df49d0d8ad1d55cf9bdbbc50e1a0322ba0ee42ff549aa07f767642'
stream += 'e7e8825ae78604b32d9caaae0c1e687c617d722fc2b1215483cef045e67913e95ab9f5f4871430c3b8bd7544dbe6ec30a07f44734aacb854ab51f766'
stream += 'ca39e08fd4ad7577bf59720a2a0957eed80247926b97370f8fc7dda96c735f49cad558f91f0cdeeed8564a22cc0063c62cae4b89e04ee66116708fcc'
stream += '9eff75d7098cb1b689d8dc5b67c165270b6733e6ea4c199d181dadab57bf9aeeb41725d57061c349085c4611e298b51a926196a8a97f881698dbf5ba'
stream += '92291cb10d0d0dbecee89d11f3bd29e52835efb49d4c405e5b7576e501c3c1301439a2ae505fa650b7b1a7d1bc0499bec64eaf0d3dd598d22e945173'
stream += 'dfd878de05c940d0c48f47ee8ce0b401d4fd20c852c1b993d4c657eead9cdc81bb7571c5803e51fb0a30d73d0d45cad33b94463d5d4cbb33f70c3bd0'
stream += '71216fd8dfea92b0bf3478bcce03768c8d9ab17138b6cb6344d9d10f9545fe72dbbb598fc5a508ca56bbb7a8ede7a181fba35cd6926a71ecc645d2e4'
stream += '991426d855897fc49b0e6a07296b0fb9d57c68fe8cf474484f38fb6481149456790b1cf20e7b3c65db03d2952a1baf637c32bb48b69d80593a1b5dac'
stream += '92f6abc4024cdade6e752c4cfc9aa0d5e14394ade464bd29bff420a87d4fccd36d84130f0e232bbde675f5d96e7a049acd95a4255cbfd64247ad3225'
stream += 'eeb6f6cbce17dcca1abd48303de27852a114411dbe65e7173e63031caaaeaa44e0263cb1d39fa707f7a5d744ac3a1ff955490494dd0d25f4d425fec4'
stream += 'ad362c0ee4159c7cf12abbf2374988dbec25665365940ef2ce945757c2e3e381037b74c23c0bed6865831d94cef342b669bc3546880e93a3a693b638'
stream += '62e587d125fcddd3d84c243e3cac12543b53345a29f14a9e0c7bd5ab59cc9622192224b626df25dff1b348505435d3c7e6321c98542f71deca0620c4'
stream += '7790dce4a64b0e7366a1f27382f1465695047d51631d109125c18e85d78cbe7a892318b7e83f8290b80694fd48d264dd4182aab1d1ee0a26934c7c5e'
stream += 'ad35d8121aee52ae734ab1cd895368982c6baaa76ec024d53a5b0cf05ba3a1058a3fd50ae9f22d021009bddf9b244da70a14fee233b4525c26586513'
stream += '5559465827799b3fd280d965202034e0ce1f5bad6eb26182492f76059a103a137281baec82e2c07cbbf238164888a80e181c39953b4cf47c5315f72e'
stream += '1d322a39933dff08fd51a2c7c79f489265b7bbedc5fe03d43d7b99fabce55fe8016117c6b64d20f16c014932a2bdaaaf749e3ef9299bbd6a220e6498'
stream += '4182220218b6d84685db558c0c58ed114a4f3efd2a4d244db4b2382c3a0448cc0ce622d79fe57293ff2ae65fa52384b7596b23f4044935782e471218'
stream += '6ab0dc8ea367129e091367845166597e3f86ecd5b823dd1a2475d72e84d95f78101d5f4d1cac9efe31a41138b181856514c4440aaaf0f9595eb01696'
stream += '9670dc3afeca319fd5429b08a9d200203b361d81578fe27e78fb94b87dd88e893163124fb2ded4d5d20128df985b16fcf63bee8d3670534d67a282ea'
stream += 'c9a13fd906b4370ed2ebd81320c7cdf3c7ec62967696cb859927517dd3c8fcdd51a9f2276494d76beccd469f00034ab4f25b5e84d7c6cb36b23f51ba'
stream += '7958294f14fe9f8188d4a90ba3fccf0b40950c73ab12e38561830e522c461f8d37e61ada7d2f89d3c9bd9d89f3bc86736db111f5cefc97e64073fdf2'
stream += '8af9967033c7dc8598c09c42afd7fae6a83cf54acb989853c3ee447501eb5739c9e1be3d81d7f9594fffa1166e44fab0c37418fc7102a42cbc56cc00'
stream += 'e53eb68d3579a0258b65c6918d43340b4b6cd9b4a810a55f97521a7d2a6125596ab309c4e02ba5cb0d0e75fc153fad7fe325a4eb270d0884b0d2f50d'
stream += '45cd54fb4026af2e538c5b8732f7a9d5dc5f763cf0d1f33dea2f9e822e0bf90745b0992d6667822390eef8826ce01ab1a06fdccf093c937dccea66ed'
stream += '2ec32e6dff20c9e3cb231bdaa3c57de6cf2777e6ed5e6c396db3327b58588c97d4e4ea4fd6980e69e7366dad233947a5952c6159e3e1de101d821d72'
stream += '002c427f9de3ebee1abb65ee4154ae4efba21c93c28b2b763722325f63ea64eb4cb52c58943b85001adad44f9810ae04fe6e0695d62fbfc013bfcb00'
stream += 'ce057d97363acb0a48eaad48cf7d1a1801125eb6a042b25765a828f025e5ff788d7bfdbebf849bcb7bd5fade1497a72986c7b9f11548185a5c1effa9'
stream += 'afee048920e0173ee5211877ea410ece0254c51b6a1913041250c84771d966d07198a6654cd47be644c5d24785267b62fcb58a7e7849faca56fc08a8'
stream += 'a76e01f76e0ecfc7c2ae507b54f39c8a6389227b37fe005838dee1b1f64d41a7dc1b2a6ae34bec0fca5fd98e04566e5192b99d4a1bda0040328509be'
stream += 'b9150abbe72c9da0a0753eddad11e2f8a9b823930fb41082d6ef4198c392e54c59b3e11211f10867870026dabdf9265e2e98e667bfc6c718907de25b'
stream += '72ce2aa9360fbc4fdab77de070a286976be4c9563edd9b7b8744032ce454e1e24569d2f778cdad6de4db49acdf6becd9aaf97dc439355d0cb79bbf64'
stream += '5ac5d93fc8952070d7d9a1dd9a0b7cde0cf58283ea0d155d88996ddd4a89c1ff6a4901bf3335665b2090e1e8857f59b52f94c0c0af49d8605587ce23'
stream += '77007071d78bd2da3d6f500b007c006d785eda6060d061d72ca2fbbfab7ec5e76ebf1473a42d66ad36df15afcc575f42e3cf061a380b9609cd7ef1b1'
stream += 'f3bc06c5b76a49082020bde388f87b6d49a677ead17611e33de4fa0476d367df03d647ba1c84c3678b5d59aa63fe6319e5998ab7b5771db480d48d7d'
stream += '1645ca0979183b38966f9dd6ff9f2cc323f1d78ccf5705e460ccbeba70da1917b2b5a6132a548d0cfc254159733f8666bc4beddddb0eb2dc9bc6e497'
stream += '30bf861c8c7370d156cc9789f2547bcf2d15c0429aa20e98769424ac08388ae7db582586626c71e2085f02375b25a41a7a96576ef222a53003a1e3ae'
stream += 'a24fe80c99b5e42ce826b788c806049f0d67fdff86622a2e79f2a3adde81b3e8c57b9dbaecc682d3caaaa68df97cc5e59fa3b72d64b24f4252e3fc3a'
stream += 'a7d1adb481c397a38400379b4ccb225cbaba2953a5dca1b1cb786b01dba7ba6f1cd70c527a6cc38de538a5694013951b11c4625d7a35298a84cbb644'
stream += '5362a93173938c6960524e6a969912d2315f20a069daa75851538a62c6c5867385b08f4418c024a5d17f69444ef9fa4a34994126356e2dcdf491a58a'
stream += '8c72418a15906c5c88a88cf6454fe5fd1d405229749384f8e3c10d3786edb29746bc087c956d01c63e2b13b4bf280959218be9b72e3a78589378086b'
stream += '8e06420f6420a2090f56f40c29839eb8925b4d7580fd912601caf750d5e05eb73820153a96cfdd6c771359e1528a81561021677b0046f521403218a3'
stream += 'd51f917de2ea57952d610d8e8ece093385cd84e4aa1d4c0b21df558055f9b46b59e062f538bc54475e96cb7530a99f2533ec9a50fabc9b3636e7d50e'
stream += '940380a31521fdd6643fa56ae8d4359580696d80291b07a210f582b107224675eef361af58ede40b2c040d381e088919a53b137c1d813fd0e6561671'
stream += '27d2a097101396fc9b8c8f692792e1004f84a1f5400d2f20474557aad75588e696980c580674fd352ef766e6cb9a8a19e73bede400b625c017f3c630'
stream += 'd07ea1c54ca8b87b517942b66e9abba802745dff98cf8a8fb8839dfd1b257260590d330890a557d797a33f14374aa916fa7b5db4bc205de64184abd6'
stream += '6533e5cea0b5e1141ef8bfb380f4267b50752dac5f8753209676586207891da31ae218362f91ed74cc5771ba5f2b84fe0e69d7c958bf58178ec0e047'
stream += 'b8cba4d1d39b8be156dc7a43717a668c8539f2f5cb640d67c1c1d445696bc4382485e0b5b5d96fd6dfe9261ca9b8e6fe874ee09d33bbee22a16fa13e'
stream += '9df931faef02b3da9a25b977c8c01ac785b4c9a5eeb9a59f78c3a976d6a21df9cd8fd122b99defd367f2fc3375f91d8125b2bafeec235b95d5d2a3e7'
stream += 'a096dd20a36083245c74371b8250346d27e1c115623eea2c66f9a4ec33e6401bde4c68460ab0708866340a15833b04776d4199d71f3c296b5a409ac0'
stream += '053c29fe94e799e3a43435cd719d23b10d11e3327cde17cfbcb28da13b7fb7db9f038cd9509a0c9117702be57f16fd93f8f800f3c5ca816491cb0ba3'
stream += '49b65206d768a6661f349b7ae3179462b351e0c3e3628f72f02892ae31a2e72bd8db023984f35664ea8fef4bd2f17cd0cec5c4fca7c35efe7552c583'
stream += '582781b107152edfd454b006a0f9d0cc39aa77b43c6436be9ec776b4b7d7552be92d664a2271c8d6593c5ac9d99c40b443aba812f02c77a8bf7f51dc'
stream += '91e13f9a933a8cca0aeee6af0195c5cda1cd2a806e52aa944cc72b938352da2f524c6a3504f355a88a142ab50fdfefa3803322acc86d6f66c6120c68'
stream += 'ad14b2f0940b8b79ea3b5231c631e6186bb07c4ef93fbcd0237ab06aa069e56db78337458f767166fa5de89b5475ad75e06485c02f103404a404619b'
stream += 'c6f38dbc0050fcf553e153aa7e19367df394437dcbd91c37d8020587530d1a45b9a5ed76a66491d5b308a185d556e3abb06c8744888a8d1ac57ac490'
stream += '5ee6b076fcf552f33d3efd32b8857dbaea42397e6cbf2c706d6d674f52fc8ea193a093008d7c7dab0440b97ac95223a3fd80d0ddb1eecdbfc3046545'
stream += '2da89c129f15d9a165b83ba4edf41064d4a3006adb4167158cebc5e94c96a1cd20818bbddfcce2d62f67e36e1c6b9150ea01ad2c834257ce01dec049'
stream += 'b2bc5d1528feb7400a353b49926944cebb1286fd3a7829c76a948e45d50119bfb8fcdfda8380ad7bb4950b6fe5fccbb50939d6fd801a00e157a693d0'
stream += '4938dc498538c6f9a56157ff4cf1efa517fa173904d16b9b5bb3289127fbdfa30a4a66d340c87f04b53c1ce407dd0d8f3a63b8ce9bb211881b5b9808'
stream += '6c6848cfb9635bddeebf6bafc74771f7b2681f3ec6d32fc31a1bd9c8284714d88ccd2a4a8cf6961f0c7c83e115ad982606cf42707202ba0860e83fbf'
stream += '9a9a7b594d1a60ccc6bf6b637ab95e461decac0810b7eea88a9e25c8cfb2b9d2e0a83802a70bab37b627ff7f98375a260a5ac2cb0637294956874c28'
stream += '3b97cab4616c8e297a7652bb8043c891e5242a7fff99becf6ee8a8090b8f96b7667b666679d6f25f5a52c42ce02100cd4cd2dd7a1e1ce493fdb41f59'
stream += 'fa18f4e35fd6cd74f3b005ca852afa3cf086cc0b90291711e6fc0c186231dce1be644a599435b8872f7ab8c63a38d92db5cc944ecc7b3a96dc603bc8'
stream += '7fd09edac53f19104b74b215178045053dc4e1d1e919e44e920f49f4e73417be50a9ef64d54f65feea6207c7caaaaa8feb9608fe8de3c473d134a092'
stream += '42f52f146eea15844e7652aa5036c7254fd2006d8b57074cf5ac2f8a916592b6ad926910b22ade6e7797ac5be196d10bb5851719c8dc547657180647'
stream += 'ff701df8f9c574b29715de17c16f57d26a084f83bbff21b72bc67af4fc505f7879cfe4b4132952eef7e6a111425b20507e45f4478ce99882db0235b3'
stream += 'b68b7bc0ec7f2a20e9291c82aec433d704bef5cb71406ac9172988df7aacba40eb257c2c4e2fddfab8e9a8ef884716a26e96848d9819841ab0855c2b'
stream += '76aa319c170637afa8b0c86e2b3493b675b4b83ab684205c67e1abce31e8e486a8406493251921ebe834e32a49874240289c31563c39be5fa7d73e3c'
stream += '6dc4060943e4714f477bf785c2e8bc73a9c6cfd12210e7d4c13deee8cb92f3ccff3131af4913b7edb3dc5ea5e5969dce60522dc5bfc1b250cf53550b'
stream += '4cd929b10a37d91f8bc9dfcd43fdfff1e72689aa415204924b1d73a047a92f69e02f286ba928fba152347ee9e459e2cb51eef3202c5281c7c8dd53f8'
stream += '507e34f9edc0eb86dfa258f4ae6971bd20da0ba1b3f9223dada9a8e05634153611475a11ce2b670ba4d01dd8782925748c31850659d23d67d28884a2'
stream += 'c854404a04dba8a41a8c98e06f2c0a280427e1beeaae44fad98b077d900b6d9f55ddc59ce9543f5c4b7be31e3e3491e485ace8047e65cf5b51684f87'
stream += 'dad986729e7a6b2f94703109713dbd77454ed950882835d705baf9997d59ead5b0adbaa734f2539e990ae0672eb83a290ad95e6f1a4330a0f6bcb7b3'
stream += '41d4429c223091427adaaf48c69c8c59011d7dad040a2ce5816085dbca8a532ae267c77565665044e1c905a8617b00f8e7d3ce393845f51fd58ae160'
stream += '43c72f82f5e2bf2486b6ceab75fc4bd5e02f217fae2cb80c035d7289af39537699a844e9e4807fb01df4a2c87aacaeba9fbc02735a9ec6c013f907e2'
stream += '9e6c158615eab92c7cc12265a7dc0f060421fb4ca70dafc80dce47daa42af4432248f995c2f446e31efdbef26aeb6eaae9442275aba397364a83882f'
stream += 'f45a05d11391f4499a22783bca612dc61c9812063c24a8b9b2cbe16af31931f63091888eb8bca0b71861a92000ffb72bce0206fd730cd35267f74d7d'
stream += '8d449ef5dc1c5100df72b0c921c48c32a91c0b7b409a07103eae14991e15f870252af33fb95a3147c75871ff7de2e3ef229d95fde60fb17960d1af8c'
stream += '975c80646f09326e7f1bf7ad4746c0a97abf813936b782320f32dad425cbd6299788ef7bbe81ce9ddbf07833949c5380e932d73509dba78efd8682d5'
stream += '066437e36d0e2febd7d5c0fd47596f5ad0db378af06f456317965168a4cf605de5c94f65107fe2c32d5cbb3237b6651923056ba699fb757df6da86d7'
stream += '79a899f668ab9ce6ca5a64f85bfe2a00153403d30c543a7ea68d1c475945a4b138b9d68ba0829d736314c965845e9022738c65d20388f21a7bbc1077'
stream += 'da441d9927b354298d183517d7e0c7304bdf14259cf56837b23fd9c78dad0d47efd021c29be31b360faa0b1cc00e96bd3cc015a92fff2d8a4b86c133'
stream += '57fd9b5179402e69f19736401f7a3ca75cecd142eb2dcf4f9fae4d5291fc9cbd1d59ea355eeb6a761092f31b013eb31ad4bd35775b48a913b336f0ab'
stream += '83105461586fa1a3caf93ca9141659eee18974674a68735e5e27d3bd6aaeb3e0a66d5998d95f125d33a53baf84827a689e9fdec36cf9445af99f99eb'
stream += 'a692f7dbcf1b58821e31469cc94ce0b6ce372492fc1efb6578e528f642fd5988dd206f11022683bdbd8073b79b77b34cddce81496bbfeaf627078f25'
stream += 'b3573dfe5e37f40d251d8af2f1cf321dba17a8373642d71db1ed29db5941df01ebaddfa157a2b750b98b647af2bf785e5cc83b8088728e8a560d2b08'
stream += '51e57e5adc719b087c082360570a9efbfa4715651078141bab8b58acb0bec9087af6db2a4abf23d800d743c8cade4f02d949742c00d2b22cfad8d977'
stream += 'c211d5cc5d2b5c75e17210f76ab711513ad6b7e905329a76b7cc6acc5f9861be20132ffb4e0da5fc568312ad2d40edc7489fa3a190a5559e12df5afb'
stream += '362fd3b67dab874314a804b0a510cf64cf64f479af71c106a208f05d89e21308190795deb9b179fcee275f5d77c1f0b4e1844a0d1fd0de370ee49351'
stream += '171145dbb88491fc9f5443cd2b8065b846349fc869bf7fbada55988f57cb51c534a226f93a3c5e58b5478f073c9bb3444b81189df6346b06d8c7d380'
stream += '1bdc417c89c3f037b2ca60469d09110865f35aba261f7f3f0241b4fd252146ddb80e416f131269e9dcf4d134a11c1c0e0f136f04bf4657204ad349bb'
stream += 'b33442d99fe9560d1558cc20936877ef77d62771df37116ffb6c31c872de5952a19d530703a98133629a1aeeffc37b60d0587293dd43e43bcf175d57'
stream += '09a0879454b7c7e80ebfbd3f030b2420deb0b664f8900f1939a7f611b01ad92d539d448f4a1f7cba8f9738f353fa038258666d73c4fdbff3dc122321'
stream += '9fd3dd4820baddc7aa9e3434745938d9aa2dee71e119228ba6eef0ac014eedad9033bc28741d29a7c98c68441143fba8a8016a13068529dd135d01f9'
stream += '1dd8ea549ea2af7aaff01c602f226a2bb29e46b8b191640bbbe4e5d31c3a04fe2d2c44992a2d68279e346d7385eac6d59eec08c2b2bf5adaf17ab42f'
stream += '55f06eb10581d7a8b730768a784f0bbcb94222f1155f912e6424fbb51c80e833e8d8f78d2229a8fb9e51dc05dc90659e1e5b22993e12f7bbf28cd948'
stream += '3c41ca5930763d25bf9b0d7c211bdb65310c9f617fad30b03adf303fa4a853052d5ae077f9be6ad53fe29bf6ae43b97eea9d9524b2a6bb32572f38de'
stream += 'c080ff67a537153b373383f33056e1a59f0730dcbd99d60b2165b4c043673e747bd885d6177fd4310dde0fb0ab8ace560273cf20ccebf04dcba0f89e'
stream += '1d24e5d1f0755fea07800de84475bcdba38078a6a04b8def1b21be0c4c80e92aa80399e4d2223eadf0458e8a1edf12745618aa6c20f0d429e7000e94'
stream += 'c06d95376ca92ac13d9b9564c5859e86a544cad717156aa256815dd116f34c542c60804c34311ed582f6febaf633e80c7ce8f5fa34a82ac7aaa0d993'
stream += 'c9b67ec2a44ee6dfad48fc8db1e8afb861fe750dcb324a09648d75cb527e1bd17a9bc1d60cce2b28b635bbdaa52c2fba2a5ac18737a59643bd2f32b2'
stream += '39fbbc8ada2ffa9d6ac10276274a5823e3a866c0d98c2c0dc5334bc5102fc91bea7001d124063634d9f22955094b82f6cf82ff22a2679dbbc4307eb8'
stream += '2d96fd6920801476ecfbf412a024445d080c1b3079f60ae484fd8214516c2dde011f5c0882f60e2c753a01f3e761ac32a5981beae530e851f4aff9bb'
stream += 'a328e655ebc76b2c6a92c25bfd8141f762abb0d877df5563a0300e42897aee78a2c0ec05d8faa5f633148534246d12eec5a488ceb16495faec22137f'
stream += '7abcfe19eeac83af668b54c9ca11ff3fe6bc35d7817c620864cbfcff0027075f93185197a08e3a0b8efaf70859dfa08cc3d1c7c9e7c8ee95ea469649'
stream += '4443f318cf7475fc28cb63feeb58130fd5296a56bfcce0ae96ad1c0723edcfc08c6f44176928eca3f5dfd9610e4de5e4d129b554a5c526d38e4088ec'
stream += '0c48ec037ed05356f2687f7a33551c3ac15772cea4ebc764549f0a18e6fc6236bfc481662968caea5435334bcf4c27c7369e0f59c0729c48538611fa'
stream += '2594e0ad63b410d39a36760fe5dfc0105e2a87b51ffcea4eb70ef55969e59fb7ba41700d93cb590ca73335a00a333515819d9d4740b25b933f4ba4ce'
stream += '8a65f0365072a88e478330dcd751028fc5a084ee0c01568a47905473fc5346bab0eb7c097bc73f8119ddfbff755f8b2fa1fe28982a84ffdcf921a7be'
stream += '98ffc2a7e1cb27ad9ba45a3aaa6ee19a9ef5f1df65459df4b27eaffa87d7cef2'
stream = unhexlify(stream)
