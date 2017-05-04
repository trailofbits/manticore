/*
 * DEFCON CTF Quals 2016: baby-re
 *
 * Note: Challenge was ported to use read(2) instead of scanf(3)
 *
 * To run:
 *   $ manticore baby-re
 *
 * Look in the output directory for a .stdout file containing "The flag"
 */

#include <stdint.h>
#include <stdio.h>
#include <unistd.h>
uint8_t CheckSolution(int32_t Var[]) {
  volatile int32_t C[169];
  asm __volatile__(".long 0x022802eb");
  C[0] = 37484;
  C[0] = C[0] ^ 1;
  C[1] = 172968;
  C[1] = C[1] >> 3;
  C[2] = 14992;
  C[2] = C[2] >> 3;
  C[3] = 46273;
  asm __volatile__(".long 0xd94f02eb");
  asm __volatile__(".long 0xb75102eb");
  C[4] = 50452;
  C[4] = C[4] ^ 221;
  C[5] = 43166;
  asm __volatile__(".long 0x88b202eb");
  C[6] = 118216;
  C[6] = C[6] >> 2;
  C[7] = 65552;
  C[7] = C[7] >> 2;
  C[8] = 57693;
  asm __volatile__(".long 0x30d902eb");
  asm __volatile__(".long 0xce2d02eb");
  C[9] = 7313;
  C[9] = C[9] << 1;
  asm __volatile__(".long 0xe25d02eb");
  C[10] = 21068;
  C[10] = C[10] ^ 46;
  C[11] = 39342;
  asm __volatile__(".long 0x208602eb");
  C[12] = 54757;
  asm __volatile__(".long 0x017b02eb");
  C[13] = 814976;
  C[13] = C[13] >> 4;
  C[14] = 76944;
  C[14] = C[14] >> 4;
  C[15] = 6019;
  asm __volatile__(".long 0xea8402eb");
  C[16] = 38962;
  asm __volatile__(".long 0x0df702eb");
  asm __volatile__(".long 0xfc6c02eb");
  C[17] = 7397;
  C[17] = C[17] << 1;
  asm __volatile__(".long 0x999e02eb");
  C[18] = 22536;
  C[18] = C[18] ^ 79;
  C[19] = 837;
  asm __volatile__(".long 0x9b1c02eb");
  C[20] = 73454;
  C[20] = C[20] >> 1;
  C[21] = 50592;
  asm __volatile__(".long 0xcc4602eb");
  C[22] = 11829;
  asm __volatile__(".long 0xb5cd02eb");
  C[23] = 20046;
  asm __volatile__(".long 0xffae02eb");
  C[24] = 37024;
  C[24] = C[24] >> 2;
  asm __volatile__(".long 0x92cf02eb");
  C[25] = 26614;
  C[25] = C[25] << 1;
  C[26] = 619680;
  C[26] = C[26] >> 4;
  C[27] = 105886;
  C[27] = C[27] >> 1;
  C[28] = 135056;
  C[28] = C[28] >> 3;
  C[29] = 26907;
  asm __volatile__(".long 0x231802eb");
  asm __volatile__(".long 0x5b0d02eb");
  C[30] = 22223;
  C[30] = C[30] << 1;
  asm __volatile__(".long 0xbd2902eb");
  C[31] = 18533;
  C[31] = C[31] ^ 204;
  C[32] = 65221;
  asm __volatile__(".long 0x519402eb");
  asm __volatile__(".long 0x18d802eb");
  C[33] = 47431;
  C[33] = C[33] ^ 240;
  C[34] = 17702;
  asm __volatile__(".long 0x7cca02eb");
  C[35] = 33910;
  asm __volatile__(".long 0x9b5902eb");
  asm __volatile__(".long 0xbc7902eb");
  C[36] = 21327;
  C[36] = C[36] << 1;
  asm __volatile__(".long 0xa7a602eb");
  C[37] = 5222;
  C[37] = C[37] ^ 157;
  C[38] = 11469;
  asm __volatile__(".long 0xd05b02eb");
  C[39] = 230988;
  C[39] = C[39] >> 2;
  asm __volatile__(".long 0xd22a02eb");
  C[40] = 23810;
  C[40] = C[40] ^ 83;
  C[41] = 52032;
  C[41] = C[41] >> 1;
  asm __volatile__(".long 0xa7e802eb");
  C[42] = 12585;
  C[42] = C[42] << 1;
  C[43] = 54317;
  asm __volatile__(".long 0x81d602eb");
  C[44] = 32337;
  asm __volatile__(".long 0x741302eb");
  C[45] = 42596;
  C[45] = C[45] >> 2;
  asm __volatile__(".long 0xa2d202eb");
  C[46] = 34701;
  C[46] = C[46] ^ 120;
  C[47] = 146736;
  C[47] = C[47] >> 4;
  asm __volatile__(".long 0xbecd02eb");
  C[48] = 22951;
  C[48] = C[48] ^ 224;
  C[49] = 34484;
  C[49] = C[49] >> 2;
  C[50] = 1268;
  C[50] = C[50] >> 1;
  asm __volatile__(".long 0x7eab02eb");
  C[51] = 5932;
  C[51] = C[51] << 1;
  C[52] = 14005;
  asm __volatile__(".long 0x7df902eb");
  C[53] = 16323;
  asm __volatile__(".long 0x7ef002eb");
  asm __volatile__(".long 0x82da02eb");
  C[54] = 43993;
  C[54] = C[54] ^ 101;
  asm __volatile__(".long 0xcadf02eb");
  C[55] = 17335;
  C[55] = C[55] << 1;
  C[56] = 54889;
  asm __volatile__(".long 0xbc0d02eb");
  C[57] = 12282;
  C[57] = C[57] >> 1;
  asm __volatile__(".long 0xcd0302eb");
  C[58] = 35394;
  C[58] = C[58] ^ 33;
  C[59] = 61977;
  asm __volatile__(".long 0x472b02eb");
  asm __volatile__(".long 0xcfe702eb");
  C[60] = 28053;
  C[60] = C[60] ^ 115;
  asm __volatile__(".long 0x8fba02eb");
  C[61] = 21593;
  C[61] = C[61] << 1;
  asm __volatile__(".long 0xfc7802eb");
  C[62] = 29838;
  C[62] = C[62] << 1;
  C[63] = 31156;
  C[63] = C[63] >> 1;
  asm __volatile__(".long 0x545902eb");
  C[64] = 25041;
  C[64] = C[64] << 1;
  C[65] = 163040;
  C[65] = C[65] >> 2;
  asm __volatile__(".long 0x225202eb");
  C[66] = 11007;
  C[66] = C[66] << 1;
  asm __volatile__(".long 0xcc8802eb");
  C[67] = 6804;
  C[67] = C[67] << 1;
  asm __volatile__(".long 0x99a902eb");
  C[68] = 5061;
  C[68] = C[68] ^ 151;
  C[69] = 214000;
  C[69] = C[69] >> 3;
  C[70] = 31708;
  asm __volatile__(".long 0x4f0702eb");
  asm __volatile__(".long 0x4ef102eb");
  C[71] = 39583;
  C[71] = C[71] ^ 44;
  asm __volatile__(".long 0xea1402eb");
  C[72] = 13694;
  C[72] = C[72] ^ 92;
  C[73] = 59055;
  asm __volatile__(".long 0x3cac02eb");
  C[74] = 65476;
  C[74] = C[74] >> 1;
  asm __volatile__(".long 0x20b302eb");
  C[75] = 29347;
  C[75] = C[75] ^ 62;
  asm __volatile__(".long 0xeea802eb");
  C[76] = 10450;
  C[76] = C[76] ^ 147;
  C[77] = 15650;
  asm __volatile__(".long 0xbc5e02eb");
  C[78] = 189996;
  C[78] = C[78] >> 2;
  C[79] = 57856;
  asm __volatile__(".long 0x481302eb");
  C[80] = 13477;
  asm __volatile__(".long 0x480702eb");
  C[81] = 20438;
  C[81] = C[81] >> 1;
  asm __volatile__(".long 0xf45902eb");
  C[82] = 4930;
  C[82] = C[82] ^ 234;
  asm __volatile__(".long 0xd26902eb");
  C[83] = 21229;
  C[83] = C[83] ^ 194;
  asm __volatile__(".long 0x5e2a02eb");
  C[84] = 29604;
  C[84] = C[84] ^ 3;
  asm __volatile__(".long 0xc9df02eb");
  C[85] = 55130;
  C[85] = C[85] ^ 147;
  C[86] = 24260;
  C[86] = C[86] >> 2;
  C[87] = 64188;
  C[87] = C[87] >> 2;
  C[88] = 36432;
  C[88] = C[88] >> 3;
  asm __volatile__(".long 0x1c7c02eb");
  C[89] = 1131;
  C[89] = C[89] << 1;
  C[90] = 18903;
  asm __volatile__(".long 0x885602eb");
  asm __volatile__(".long 0xeb6102eb");
  C[91] = 65297;
  C[91] = C[91] ^ 154;
  asm __volatile__(".long 0x817602eb");
  C[92] = 17295;
  C[92] = C[92] ^ 152;
  C[93] = 18820;
  C[93] = C[93] >> 1;
  asm __volatile__(".long 0xc1b102eb");
  C[94] = 11257;
  C[94] = C[94] << 1;
  C[95] = 209508;
  C[95] = C[95] >> 2;
  C[96] = 18470;
  C[96] = C[96] >> 1;
  C[97] = 53309;
  asm __volatile__(".long 0xeafa02eb");
  C[98] = 383272;
  C[98] = C[98] >> 3;
  C[99] = 59111;
  asm __volatile__(".long 0x0ba802eb");
  asm __volatile__(".long 0xf93a02eb");
  C[100] = 41430;
  C[100] = C[100] ^ 159;
  asm __volatile__(".long 0x2bfe02eb");
  C[101] = 12211;
  C[101] = C[101] << 1;
  C[102] = 41178;
  asm __volatile__(".long 0x033702eb");
  C[103] = 23447;
  asm __volatile__(".long 0x551b02eb");
  C[104] = 7220;
  C[104] = C[104] >> 2;
  asm __volatile__(".long 0xc9b302eb");
  C[105] = 4350;
  C[105] = C[105] ^ 217;
  asm __volatile__(".long 0x45d602eb");
  C[106] = 8450;
  C[106] = C[106] << 1;
  asm __volatile__(".long 0xce2802eb");
  C[107] = 33371;
  C[107] = C[107] ^ 62;
  C[108] = 187068;
  C[108] = C[108] >> 2;
  C[109] = 58551;
  asm __volatile__(".long 0xbb6e02eb");
  C[110] = 34118;
  asm __volatile__(".long 0x9a6002eb");
  asm __volatile__(".long 0x7c6602eb");
  C[111] = 44865;
  C[111] = C[111] ^ 57;
  C[112] = 11933;
  asm __volatile__(".long 0x58c902eb");
  C[113] = 82120;
  C[113] = C[113] >> 2;
  C[114] = 125592;
  C[114] = C[114] >> 3;
  asm __volatile__(".long 0x680702eb");
  C[115] = 36459;
  C[115] = C[115] ^ 158;
  C[116] = 18231;
  asm __volatile__(".long 0xeca202eb");
  asm __volatile__(".long 0x03f402eb");
  C[117] = 42924;
  C[117] = C[117] ^ 17;
  C[118] = 61056;
  asm __volatile__(".long 0xc01b02eb");
  C[119] = 45169;
  asm __volatile__(".long 0xc93902eb");
  asm __volatile__(".long 0xf4c102eb");
  C[120] = 20642;
  C[120] = C[120] << 1;
  asm __volatile__(".long 0x978e02eb");
  C[121] = 861;
  C[121] = C[121] << 1;
  asm __volatile__(".long 0x8f3d02eb");
  C[122] = 26574;
  C[122] = C[122] ^ 249;
  asm __volatile__(".long 0xaaaa02eb");
  C[123] = 47043;
  C[123] = C[123] ^ 15;
  C[124] = 42363;
  asm __volatile__(".long 0x2f0002eb");
  C[125] = 120264;
  C[125] = C[125] >> 3;
  asm __volatile__(".long 0x41d802eb");
  C[126] = 19101;
  C[126] = C[126] ^ 130;
  C[127] = 10788;
  asm __volatile__(".long 0x59e802eb");
  asm __volatile__(".long 0x1a6802eb");
  C[128] = 33422;
  C[128] = C[128] ^ 169;
  C[129] = 63680;
  asm __volatile__(".long 0xd6a802eb");
  C[130] = 148340;
  C[130] = C[130] >> 2;
  asm __volatile__(".long 0x1bee02eb");
  C[131] = 51549;
  C[131] = C[131] ^ 219;
  asm __volatile__(".long 0x387a02eb");
  C[132] = 8899;
  C[132] = C[132] << 1;
  asm __volatile__(".long 0xfe6e02eb");
  C[133] = 10102;
  C[133] = C[133] ^ 249;
  C[134] = 104776;
  C[134] = C[134] >> 1;
  asm __volatile__(".long 0x638902eb");
  C[135] = 6373;
  C[135] = C[135] << 1;
  C[136] = 12587;
  asm __volatile__(".long 0x470302eb");
  asm __volatile__(".long 0xab3802eb");
  C[137] = 29393;
  C[137] = C[137] << 1;
  C[138] = 66152;
  C[138] = C[138] >> 3;
  C[139] = 45226;
  C[139] = C[139] >> 1;
  asm __volatile__(".long 0x5c8602eb");
  C[140] = 30792;
  C[140] = C[140] ^ 105;
  asm __volatile__(".long 0xbf1602eb");
  C[141] = 20863;
  C[141] = C[141] ^ 10;
  asm __volatile__(".long 0xb05902eb");
  C[142] = 32165;
  C[142] = C[142] ^ 125;
  asm __volatile__(".long 0x5b9d02eb");
  C[143] = 36806;
  C[143] = C[143] ^ 236;
  asm __volatile__(".long 0xdb5402eb");
  C[144] = 47376;
  C[144] = C[144] ^ 222;
  C[145] = 33282;
  asm __volatile__(".long 0xed9302eb");
  C[146] = 946880;
  C[146] = C[146] >> 4;
  asm __volatile__(".long 0x66fc02eb");
  C[147] = 65118;
  C[147] = C[147] ^ 242;
  asm __volatile__(".long 0x49d002eb");
  C[148] = 9455;
  C[148] = C[148] ^ 227;
  asm __volatile__(".long 0xf1d402eb");
  C[149] = 59505;
  C[149] = C[149] ^ 190;
  asm __volatile__(".long 0x114502eb");
  C[150] = 62801;
  C[150] = C[150] ^ 249;
  C[151] = 389752;
  C[151] = C[151] >> 3;
  asm __volatile__(".long 0xf49d02eb");
  C[152] = 23674;
  C[152] = C[152] << 1;
  asm __volatile__(".long 0xffc202eb");
  C[153] = 18796;
  C[153] = C[153] << 1;
  asm __volatile__(".long 0xc5ef02eb");
  C[154] = 28806;
  C[154] = C[154] << 1;
  C[155] = 40510;
  asm __volatile__(".long 0x6b9002eb");
  asm __volatile__(".long 0xfab902eb");
  C[156] = 51817;
  C[156] = C[156] ^ 126;
  C[157] = 35879;
  asm __volatile__(".long 0xaf5602eb");
  C[158] = 63890;
  asm __volatile__(".long 0xfe9a02eb");
  asm __volatile__(".long 0xdba402eb");
  C[159] = 4126;
  C[159] = C[159] ^ 24;
  C[160] = 59511;
  asm __volatile__(".long 0xf52702eb");
  C[161] = 21386;
  asm __volatile__(".long 0x995502eb");
  asm __volatile__(".long 0x33a702eb");
  C[162] = 20866;
  C[162] = C[162] ^ 163;
  C[163] = 53034;
  C[163] = C[163] >> 1;
  C[164] = 112612;
  C[164] = C[164] >> 2;
  C[165] = 404032;
  C[165] = C[165] >> 4;
  C[166] = 43789;
  asm __volatile__(".long 0x97f302eb");
  C[167] = 51266;
  C[167] = C[167] >> 1;
  asm __volatile__(".long 0x348d02eb");
  C[168] = 7301;
  C[168] = C[168] ^ 23;

  if ((C[0]) * Var[0] - (C[1]) * Var[1] - (C[2]) * Var[2] - (C[3]) * Var[3] +
          (C[4]) * Var[4] + (C[5]) * Var[5] + (C[6]) * Var[6] +
          (C[7]) * Var[7] + (C[8]) * Var[8] + (C[9]) * Var[9] +
          (C[10]) * Var[10] + (C[11]) * Var[11] + (C[12]) * Var[12] !=
      21399379) {
    asm __volatile__(".long 0x96d002eb");
    return (0);
  }
  if ((C[13]) * Var[0] + (C[14]) * Var[1] - (C[15]) * Var[2] +
          (C[16]) * Var[3] + (C[17]) * Var[4] + (C[18]) * Var[5] -
          (C[19]) * Var[6] - (C[20]) * Var[7] - (C[21]) * Var[8] -
          (C[22]) * Var[9] - (C[23]) * Var[10] - (C[24]) * Var[11] +
          (C[25]) * Var[12] !=
      1453872) {
    asm __volatile__(".long 0x8ad902eb");
    return (0);
  }
  if (-(C[26]) * Var[0] + (C[27]) * Var[1] - (C[28]) * Var[2] +
          (C[29]) * Var[3] - (C[30]) * Var[4] - (C[31]) * Var[5] -
          (C[32]) * Var[6] - (C[33]) * Var[7] + (C[34]) * Var[8] -
          (C[35]) * Var[9] + (C[36]) * Var[10] + (C[37]) * Var[11] +
          (C[38]) * Var[12] !=
      -5074020) {
    asm __volatile__(".long 0x938902eb");
    return (0);
  }
  if ((C[39]) * Var[0] - (C[40]) * Var[1] - (C[41]) * Var[2] -
          (C[42]) * Var[3] + (C[43]) * Var[4] - (C[44]) * Var[5] +
          (C[45]) * Var[6] + (C[46]) * Var[7] - (C[47]) * Var[8] -
          (C[48]) * Var[9] + (C[49]) * Var[10] - (C[50]) * Var[11] -
          (C[51]) * Var[12] !=
      -5467933) {
    asm __volatile__(".long 0xfd4802eb");
    return (0);
  }
  if (-(C[52]) * Var[0] + (C[53]) * Var[1] + (C[54]) * Var[2] +
          (C[55]) * Var[3] + (C[56]) * Var[4] - (C[57]) * Var[5] -
          (C[58]) * Var[6] - (C[59]) * Var[7] + (C[60]) * Var[8] +
          (C[61]) * Var[9] - (C[62]) * Var[10] + (C[63]) * Var[11] +
          (C[64]) * Var[12] !=
      7787144) {
    asm __volatile__(".long 0xafb702eb");
    return (0);
  }
  if (-(C[65]) * Var[0] - (C[66]) * Var[1] + (C[67]) * Var[2] -
          (C[68]) * Var[3] - (C[69]) * Var[4] - (C[70]) * Var[5] +
          (C[71]) * Var[6] + (C[72]) * Var[7] - (C[73]) * Var[8] -
          (C[74]) * Var[9] + (C[75]) * Var[10] + (C[76]) * Var[11] -
          (C[77]) * Var[12] !=
      -8863847) {
    asm __volatile__(".long 0x626602eb");
    return (0);
  }
  if (-(C[78]) * Var[0] + (C[79]) * Var[1] + (C[80]) * Var[2] -
          (C[81]) * Var[3] - (C[82]) * Var[4] - (C[83]) * Var[5] -
          (C[84]) * Var[6] + (C[85]) * Var[7] - (C[86]) * Var[8] +
          (C[87]) * Var[9] - (C[88]) * Var[10] - (C[89]) * Var[11] +
          (C[90]) * Var[12] !=
      -747805) {
    asm __volatile__(".long 0x7b3902eb");
    return (0);
  }
  if (-(C[91]) * Var[0] + (C[92]) * Var[1] - (C[93]) * Var[2] -
          (C[94]) * Var[3] - (C[95]) * Var[4] - (C[96]) * Var[5] +
          (C[97]) * Var[6] + (C[98]) * Var[7] - (C[99]) * Var[8] -
          (C[100]) * Var[9] - (C[101]) * Var[10] + (C[102]) * Var[11] -
          (C[103]) * Var[12] !=
      -11379056) {
    asm __volatile__(".long 0x479f02eb");
    return (0);
  }
  if ((C[104]) * Var[0] + (C[105]) * Var[1] - (C[106]) * Var[2] +
          (C[107]) * Var[3] + (C[108]) * Var[4] + (C[109]) * Var[5] -
          (C[110]) * Var[6] - (C[111]) * Var[7] - (C[112]) * Var[8] -
          (C[113]) * Var[9] + (C[114]) * Var[10] - (C[115]) * Var[11] +
          (C[116]) * Var[12] !=
      -166140) {
    asm __volatile__(".long 0x5bad02eb");
    return (0);
  }
  if (-(C[117]) * Var[0] + (C[118]) * Var[1] - (C[119]) * Var[2] +
          (C[120]) * Var[3] - (C[121]) * Var[4] - (C[122]) * Var[5] +
          (C[123]) * Var[6] + (C[124]) * Var[7] + (C[125]) * Var[8] +
          (C[126]) * Var[9] + (C[127]) * Var[10] - (C[128]) * Var[11] +
          (C[129]) * Var[12] !=
      9010363) {
    asm __volatile__(".long 0x0e2002eb");
    return (0);
  }
  if (-(C[130]) * Var[0] - (C[131]) * Var[1] - (C[132]) * Var[2] -
          (C[133]) * Var[3] - (C[134]) * Var[4] + (C[135]) * Var[5] +
          (C[136]) * Var[6] + (C[137]) * Var[7] - (C[138]) * Var[8] +
          (C[139]) * Var[9] + (C[140]) * Var[10] - (C[141]) * Var[11] +
          (C[142]) * Var[12] !=
      -4169825) {
    asm __volatile__(".long 0x23ae02eb");
    return (0);
  }
  if ((C[143]) * Var[0] + (C[144]) * Var[1] - (C[145]) * Var[2] -
          (C[146]) * Var[3] + (C[147]) * Var[4] + (C[148]) * Var[5] -
          (C[149]) * Var[6] - (C[150]) * Var[7] + (C[151]) * Var[8] +
          (C[152]) * Var[9] - (C[153]) * Var[10] + (C[154]) * Var[11] +
          (C[155]) * Var[12] !=
      4081505) {
    asm __volatile__(".long 0xcb5402eb");
    return (0);
  }
  if ((C[156]) * Var[0] + (C[157]) * Var[1] - (C[158]) * Var[2] +
          (C[159]) * Var[3] + (C[160]) * Var[4] - (C[161]) * Var[5] -
          (C[162]) * Var[6] + (C[163]) * Var[7] + (C[164]) * Var[8] +
          (C[165]) * Var[9] - (C[166]) * Var[10] + (C[167]) * Var[11] +
          (C[168]) * Var[12] !=
      1788229) {
    asm __volatile__(".long 0xfb3e02eb");
    return (0);
  }

  return (1);
}

int main(void) {
  int32_t Var[13];

  printf("Var[0]: ");
  fflush(stdout);
  /* scanf("%d", &Var[0]); */
  read(0, &Var[0], 4);

  printf("Var[1]: ");
  fflush(stdout);
  /* scanf("%d", &Var[1]); */
  read(0, &Var[1], 4);

  printf("Var[2]: ");
  fflush(stdout);
  /* scanf("%d", &Var[2]); */
  read(0, &Var[2], 4);

  printf("Var[3]: ");
  fflush(stdout);
  /* scanf("%d", &Var[3]); */
  read(0, &Var[3], 4);

  printf("Var[4]: ");
  fflush(stdout);
  /* scanf("%d", &Var[4]); */
  read(0, &Var[4], 4);

  printf("Var[5]: ");
  fflush(stdout);
  /* scanf("%d", &Var[5]); */
  read(0, &Var[5], 4);

  printf("Var[6]: ");
  fflush(stdout);
  /* scanf("%d", &Var[6]); */
  read(0, &Var[6], 4);

  printf("Var[7]: ");
  fflush(stdout);
  /* scanf("%d", &Var[7]); */
  read(0, &Var[7], 4);

  printf("Var[8]: ");
  fflush(stdout);
  /* scanf("%d", &Var[8]); */
  read(0, &Var[8], 4);

  printf("Var[9]: ");
  fflush(stdout);
  /* scanf("%d", &Var[9]); */
  read(0, &Var[9], 4);

  printf("Var[10]: ");
  fflush(stdout);
  /* scanf("%d", &Var[10]); */
  read(0, &Var[10], 4);

  printf("Var[11]: ");
  fflush(stdout);
  /* scanf("%d", &Var[11]); */
  read(0, &Var[11], 4);

  printf("Var[12]: ");
  fflush(stdout);
  /* scanf("%d", &Var[12]); */
  read(0, &Var[12], 4);

  if (CheckSolution(Var)) {
    printf("The flag is: %c%c%c%c%c%c%c%c%c%c%c%c%c\n", Var[0], Var[1], Var[2],
           Var[3], Var[4], Var[5], Var[6], Var[7], Var[8], Var[9], Var[10],
           Var[11], Var[12]);
  } else {
    printf("Wrong\n");
  }

  return (0);
}
