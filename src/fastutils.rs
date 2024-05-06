use std::collections::HashMap;
use bitvec::{store::BitStore, order::{BitOrder}, slice::BitSlice};
use crate::{utils::FIB64, fibonacci::encode};

// // the type of bitstream we expect as input!
// pub(crate) type MyBitOrder = Msb0;
// pub(crate) type FFStore = u8;
// pub(crate) type FFBitslice = BitSlice<FFStore, MyBitOrder>;
// #[allow(dead_code)]
// pub(crate) type FFBitvec = BitVec<FFStore, MyBitOrder>;


/// `State` is used to remember the position in the bitvector and the partically decoded number.
#[derive(Debug, Clone, Eq, PartialEq, Hash, Copy)]
pub struct State(pub usize);

/// Result of the finite state machine in the paper.
/// 
/// For a given (state, input segment), it yields the next state
/// and this result structure containing decoded numbers and some info about
/// the trailing bits not yet decoded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodingResult {
    pub(crate) numbers: Vec<u64>, // fully decoded numbers from the segment
    pub(crate) number_end_in_segment: Vec<usize>, // the position in the segment where that number started; undefined for the first number (as it couldve started in theh previous segment)
    /// Stores the partially decoded number left in hte segment
    pub(crate) u: u64, // partially decoded number; i.e. anything that didnt have a delimiter so far, kind of the accumulator
    pub(crate) lu: usize, // bitlength of U; i..e how many bits processed so far without hitting the delimieter
}

/// State of the decoding across multiple segments. Keeps track of completely
/// decoded and partially decoded numbers (which could be completed with the next segment)
#[derive(Debug)]
pub(crate) struct DecodingState {
    pub decoded_numbers: Vec<u64>, // completly decoded numbers across all segments so far
    pub n: u64,                    // the partially decoded number from the last segment
    pub len: usize, // length of the last partially decoded number in bits; needed to bitshift whatever the next decoding result is
}
impl DecodingState {
    pub fn new() -> Self {
        DecodingState {
            decoded_numbers: Vec::new(),
            n: 0,
            len: 0,
        }
    }

    /// update the current decoding state with the results from the last segment of bits;
    /// i.e. new decoded numbers, new accumulator (n) and new trailing bits (len)
    pub(crate) fn update(&mut self, decoding_result: &DecodingResult) {
        for &num in decoding_result.numbers.iter() {
            if self.len > 0 {
                // some leftover from the previous segment
                self.n += fibonacci_left_shift(num, self.len);
            } else {
                self.n = num;
            }
            // TODO: ACTUALLY THIS LOOP RUNS EXACLTY ONCE (if len>0)
            // IT ADJUSTS ThE FIRST NUMBER (taking into accoutn the partial decode)
            // then the follwoing line sets len=0 which keeps all other numbers as is
            // ITS CORRECT as it is, but a little akward
            self.decoded_numbers.push(self.n);
            self.n = 0;
            self.len = 0;
        }

        // the beginning and inner port of F(n)
        if decoding_result.lu > 0 {
            self.n += fibonacci_left_shift(decoding_result.u, self.len);
            self.len += decoding_result.lu;
        }
    }
}

// Check with Table 6.6
// this function is used to generate/precompute the fiboncci shifts
#[allow(dead_code)]
fn extended_fibonacci_right_shift_slow(x: u64, k: usize) -> u64 {
    // calculate the "negative" fibbonaccis
    // negative fibs   | positive
    // 5 -3 2 -1 1 0 1 | 1  2  3  5
    //            -2-1   F0 F1 F2 F3
    //
    // F(i) = F(i+2) - F(i+1)

    let mut neg_fib = HashMap::new();
    // to get the recursion started
    neg_fib.insert(-1, 1);
    neg_fib.insert(-2, 0);
    for i in 3..32 {
        let idx = -i;
        // let f = neg_fib.get(&(idx+2)).unwrap() - neg_fib.get(&(idx+1)).unwrap();
        // neg_fib.insert(idx, f);

        // nevermind, somehow the paper treats everything with i<-1 as F(i) = 0
        neg_fib.insert(idx, 0);
    }
    // println!("{:?}", neg_fib);

    let bits = encode(&[x]);
    // the right shift essentially splits the code
    // the k lowest bits become negative fib
    // the rest remains positive
    // note that for us, the low bits are on the left!!
    // shift 3
    // abc.defg

    let (lowbits, mut highbits) = bits.split_at(k);
    assert_eq!(lowbits.len(), k);

    // split of the last element, as its the delimitier 11
    highbits = &highbits[..highbits.len() - 1];

    // decode postivve part
    let mut pos_acc = 0;
    for (i, b) in highbits.iter().by_vals().enumerate() {
        if b {
            pos_acc += FIB64[i];
        }
    }

    // decode netagive part
    let mut neg_acc = 0;
    for (i, b) in lowbits.iter().by_vals().enumerate() {
        let fib_ix = -((lowbits.len() - i) as i32);
        if b {
            neg_acc += neg_fib[&fib_ix];
        }
    }
    pos_acc + neg_acc
}

// fn fibonacci_left_shift_naive(number_in_binary: u64 ,k: usize) -> u64 {
//     panic!("Buggy, doesnt yield the same as fibonacci_left_shift()");
//     let bitrepresnetation = number_in_binary.view_bits::<Lsb0>();
//     let mut accumulator = 0_u64;
//     for (idx, current_bit) in bitrepresnetation.iter().by_vals().enumerate() {
//         if current_bit {
//             accumulator += FIB64[idx+k];
//         }
//     }
//     accumulator
// }

/// precompuated EXTENDED fibbonaci left shift by 1
/// n >> 1  = FIB_LEFT_1[n]
const FIB_EXT_LEFT_1: &[u64] = &[
    0, 1, 1, 2, 3, 3, 4, 4, 5, 6, 6, 7, 8, 8, 9, 9, 10, 11, 11, 12, 12, 13, 14, 14, 15, 16, 16, 17,
    17, 18, 19, 19, 20, 21, 21, 22, 22, 23, 24, 24, 25, 25, 26, 27, 27, 28, 29, 29, 30, 30, 31, 32,
    32, 33, 33, 34, 35, 35, 36, 37, 37, 38, 38, 39, 40, 40, 41, 42, 42, 43, 43, 44, 45, 45, 46, 46,
    47, 48, 48, 49, 50, 50, 51, 51, 52, 53, 53, 54, 55, 55, 56, 56, 57, 58, 58, 59, 59, 60, 61, 61,
    62, 63, 63, 64, 64, 65, 66, 66, 67, 67, 68, 69, 69, 70, 71, 71, 72, 72, 73, 74, 74, 75, 76, 76,
    77, 77, 78, 79, 79, 80, 80, 81, 82, 82, 83, 84, 84, 85, 85, 86, 87, 87, 88, 88, 89, 90, 90, 91,
    92, 92, 93, 93, 94, 95, 95, 96, 97, 97, 98, 98, 99, 100, 100, 101, 101, 102, 103, 103, 104,
    105, 105, 106, 106, 107, 108, 108, 109, 110, 110, 111, 111, 112, 113, 113, 114, 114, 115, 116,
    116, 117, 118, 118, 119, 119, 120, 121, 121, 122, 122, 123, 124, 124, 125, 126, 126, 127, 127,
    128, 129, 129, 130, 131, 131, 132, 132, 133, 134, 134, 135, 135, 136, 137, 137, 138, 139, 139,
    140, 140, 141, 142, 142, 143, 144, 144, 145, 145, 146, 147, 147, 148, 148, 149, 150, 150, 151,
    152, 152, 153, 153, 154, 155, 155, 156, 156, 157, 158, 158, 159, 160, 160, 161, 161, 162, 163,
    163, 164, 165, 165, 166, 166, 167, 168, 168, 169, 169, 170, 171, 171, 172, 173, 173, 174, 174,
    175, 176, 176, 177, 177, 178, 179, 179, 180, 181, 181, 182, 182, 183, 184, 184, 185, 186, 186,
    187, 187, 188, 189, 189, 190, 190, 191, 192, 192, 193, 194, 194, 195, 195, 196, 197, 197, 198,
    199, 199, 200, 200, 201, 202, 202, 203, 203, 204, 205, 205, 206, 207, 207, 208, 208, 209, 210,
    210, 211, 211, 212, 213, 213, 214, 215, 215, 216, 216, 217, 218, 218, 219, 220, 220, 221, 221,
    222, 223, 223, 224, 224, 225, 226, 226, 227, 228, 228, 229, 229, 230, 231, 231, 232, 232, 233,
    234, 234, 235, 236, 236, 237, 237, 238, 239, 239, 240, 241, 241, 242, 242, 243, 244, 244, 245,
    245, 246, 247, 247, 248, 249, 249, 250, 250, 251, 252, 252, 253, 254, 254, 255, 255, 256, 257,
    257, 258, 258, 259, 260, 260, 261, 262, 262, 263, 263, 264, 265, 265, 266, 266, 267, 268, 268,
    269, 270, 270, 271, 271, 272, 273, 273, 274, 275, 275, 276, 276, 277, 278, 278, 279, 279, 280,
    281, 281, 282, 283, 283, 284, 284, 285, 286, 286, 287, 288, 288, 289, 289, 290, 291, 291, 292,
    292, 293, 294, 294, 295, 296, 296, 297, 297, 298, 299, 299, 300, 300, 301, 302, 302, 303, 304,
    304, 305, 305, 306, 307, 307, 308, 309, 309, 310, 310, 311, 312, 312, 313, 313, 314, 315, 315,
    316, 317, 317, 318, 318, 319, 320, 320, 321, 321, 322, 323, 323, 324, 325, 325, 326, 326, 327,
    328, 328, 329, 330, 330, 331, 331, 332, 333, 333, 334, 334, 335, 336, 336, 337, 338, 338, 339,
    339, 340, 341, 341, 342, 343, 343, 344, 344, 345, 346, 346, 347, 347, 348, 349, 349, 350, 351,
    351, 352, 352, 353, 354, 354, 355, 355, 356, 357, 357, 358, 359, 359, 360, 360, 361, 362, 362,
    363, 364, 364, 365, 365, 366, 367, 367, 368, 368, 369, 370, 370, 371, 372, 372, 373, 373, 374,
    375, 375, 376, 377, 377, 378, 378, 379, 380, 380, 381, 381, 382, 383, 383, 384, 385, 385, 386,
    386, 387, 388, 388, 389, 389, 390, 391, 391, 392, 393, 393, 394, 394, 395, 396, 396, 397, 398,
    398, 399, 399, 400, 401, 401, 402, 402, 403, 404, 404, 405, 406, 406, 407, 407, 408, 409, 409,
    410, 410, 411, 412, 412, 413, 414, 414, 415, 415, 416, 417, 417, 418, 419, 419, 420, 420, 421,
    422, 422, 423, 423, 424, 425, 425, 426, 427, 427, 428, 428, 429, 430, 430, 431, 432, 432, 433,
    433, 434, 435, 435, 436, 436, 437, 438, 438, 439, 440, 440, 441, 441, 442, 443, 443, 444, 444,
    445, 446, 446, 447, 448, 448, 449, 449, 450, 451, 451, 452, 453, 453, 454, 454, 455, 456, 456,
    457, 457, 458, 459, 459, 460, 461, 461, 462, 462, 463, 464, 464, 465, 465, 466, 467, 467, 468,
    469, 469, 470, 470, 471, 472, 472, 473, 474, 474, 475, 475, 476, 477, 477, 478, 478, 479, 480,
    480, 481, 482, 482, 483, 483, 484, 485, 485, 486, 487, 487, 488, 488, 489, 490, 490, 491, 491,
    492, 493, 493, 494, 495, 495, 496, 496, 497, 498, 498, 499, 499, 500, 501, 501, 502, 503, 503,
    504, 504, 505, 506, 506, 507, 508, 508, 509, 509, 510, 511, 511, 512, 512, 513, 514, 514, 515,
    516, 516, 517, 517, 518, 519, 519, 520, 521, 521, 522, 522, 523, 524, 524, 525, 525, 526, 527,
    527, 528, 529, 529, 530, 530, 531, 532, 532, 533, 533, 534, 535, 535, 536, 537, 537, 538, 538,
    539, 540, 540, 541, 542, 542, 543, 543, 544, 545, 545, 546, 546, 547, 548, 548, 549, 550, 550,
    551, 551, 552, 553, 553, 554, 554, 555, 556, 556, 557, 558, 558, 559, 559, 560, 561, 561, 562,
    563, 563, 564, 564, 565, 566, 566, 567, 567, 568, 569, 569, 570, 571, 571, 572, 572, 573, 574,
    574, 575, 576, 576, 577, 577, 578, 579, 579, 580, 580, 581, 582, 582, 583, 584, 584, 585, 585,
    586, 587, 587, 588, 588, 589, 590, 590, 591, 592, 592, 593, 593, 594, 595, 595, 596, 597, 597,
    598, 598, 599, 600, 600, 601, 601, 602, 603, 603, 604, 605, 605, 606, 606, 607, 608, 608, 609,
    609, 610, 611, 611, 612, 613, 613, 614, 614, 615, 616, 616, 617, 618, 618, 619, 619, 620, 621,
    621, 622, 622, 623, 624, 624, 625, 626, 626, 627, 627, 628, 629, 629, 630, 631, 631, 632, 632,
    633, 634, 634, 635, 635, 636, 637, 637, 638, 639, 639, 640, 640, 641, 642, 642, 643, 643, 644,
    645, 645, 646, 647, 647, 648, 648, 649, 650, 650, 651, 652, 652, 653, 653, 654, 655, 655, 656,
    656, 657, 658, 658, 659, 660, 660, 661, 661, 662, 663, 663, 664, 665, 665, 666, 666, 667, 668,
    668, 669, 669, 670, 671, 671, 672, 673, 673, 674, 674, 675, 676, 676, 677, 677, 678, 679, 679,
    680, 681, 681, 682, 682, 683, 684, 684, 685, 686, 686, 687, 687, 688, 689, 689, 690, 690, 691,
    692, 692, 693, 694, 694, 695, 695, 696, 697, 697, 698, 698, 699, 700, 700, 701, 702, 702, 703,
    703, 704, 705, 705, 706, 707, 707, 708, 708, 709, 710, 710, 711, 711, 712, 713, 713, 714, 715,
    715, 716, 716, 717, 718, 718, 719, 720, 720, 721, 721, 722, 723, 723, 724, 724, 725, 726, 726,
    727, 728, 728, 729, 729, 730, 731, 731, 732, 732, 733, 734, 734, 735, 736, 736, 737, 737, 738,
    739, 739, 740, 741, 741, 742, 742, 743, 744, 744, 745, 745, 746, 747, 747, 748, 749, 749, 750,
    750, 751, 752, 752, 753, 754, 754, 755, 755, 756, 757, 757, 758, 758, 759, 760, 760, 761, 762,
    762, 763, 763, 764, 765, 765, 766, 766, 767, 768, 768, 769, 770, 770, 771, 771, 772, 773, 773,
    774, 775, 775, 776, 776, 777, 778, 778, 779, 779, 780, 781, 781, 782, 783, 783, 784, 784, 785,
    786, 786, 787, 787, 788, 789, 789, 790, 791, 791, 792, 792, 793, 794, 794, 795, 796, 796, 797,
    797, 798, 799, 799, 800, 800, 801, 802, 802, 803, 804, 804, 805, 805, 806, 807, 807, 808, 809,
    809, 810, 810, 811, 812, 812, 813, 813, 814, 815, 815, 816, 817, 817, 818, 818, 819, 820, 820,
    821, 821, 822, 823, 823, 824, 825, 825, 826, 826, 827, 828, 828, 829, 830, 830, 831, 831, 832,
    833, 833, 834, 834, 835, 836, 836, 837, 838, 838, 839, 839, 840, 841, 841, 842, 842, 843, 844,
    844, 845, 846, 846, 847, 847, 848, 849, 849, 850, 851, 851, 852, 852, 853, 854, 854, 855, 855,
    856, 857, 857, 858, 859, 859, 860, 860, 861, 862, 862, 863, 864, 864, 865, 865, 866, 867, 867,
    868, 868, 869, 870, 870, 871, 872, 872, 873, 873, 874, 875, 875, 876, 876, 877, 878, 878, 879,
    880, 880, 881, 881, 882, 883, 883, 884, 885, 885, 886, 886, 887, 888, 888, 889, 889, 890, 891,
    891, 892, 893, 893, 894, 894, 895, 896, 896, 897, 898, 898, 899, 899, 900, 901, 901, 902, 902,
    903, 904, 904, 905, 906, 906, 907, 907, 908, 909, 909, 910, 910, 911, 912, 912, 913, 914, 914,
    915, 915, 916, 917, 917, 918, 919, 919, 920, 920, 921, 922, 922, 923, 923, 924, 925, 925, 926,
    927, 927, 928, 928, 929, 930, 930, 931, 931, 932, 933, 933, 934, 935, 935, 936, 936, 937, 938,
    938, 939, 940, 940, 941, 941, 942, 943, 943, 944, 944, 945, 946, 946, 947, 948, 948, 949, 949,
    950, 951, 951, 952, 953, 953, 954, 954, 955, 956, 956, 957, 957, 958, 959, 959, 960, 961, 961,
    962, 962, 963, 964, 964, 965, 965, 966, 967, 967, 968, 969, 969, 970, 970, 971, 972, 972, 973,
    974, 974, 975, 975, 976, 977, 977, 978, 978, 979, 980, 980, 981, 982, 982, 983, 983, 984, 985,
    985, 986, 987, 987, 988, 988, 989, 990, 990, 991, 991, 992, 993, 993, 994, 995, 995, 996, 996,
    997, 998, 998, 999, 999, 1000, 1001, 1001, 1002, 1003, 1003, 1004, 1004, 1005, 1006, 1006,
    1007, 1008, 1008, 1009, 1009, 1010, 1011, 1011, 1012, 1012, 1013, 1014, 1014, 1015, 1016, 1016,
    1017, 1017, 1018, 1019, 1019, 1020, 1020, 1021, 1022, 1022, 1023, 1024, 1024, 1025, 1025, 1026,
    1027, 1027, 1028, 1029, 1029, 1030, 1030, 1031, 1032, 1032, 1033, 1033, 1034, 1035, 1035, 1036,
    1037, 1037, 1038, 1038, 1039, 1040, 1040, 1041, 1042, 1042, 1043, 1043, 1044, 1045, 1045, 1046,
    1046, 1047, 1048, 1048, 1049, 1050, 1050, 1051, 1051, 1052, 1053, 1053, 1054, 1054, 1055, 1056,
    1056, 1057, 1058, 1058, 1059, 1059, 1060, 1061, 1061, 1062, 1063, 1063, 1064, 1064, 1065, 1066,
    1066, 1067, 1067, 1068, 1069, 1069, 1070, 1071, 1071, 1072, 1072, 1073, 1074, 1074, 1075, 1075,
    1076, 1077, 1077, 1078, 1079, 1079, 1080, 1080, 1081, 1082, 1082, 1083, 1084, 1084, 1085, 1085,
    1086, 1087, 1087, 1088, 1088, 1089, 1090, 1090, 1091, 1092, 1092, 1093, 1093, 1094, 1095, 1095,
    1096, 1097, 1097, 1098, 1098, 1099, 1100, 1100, 1101, 1101, 1102, 1103, 1103, 1104, 1105, 1105,
    1106, 1106, 1107, 1108, 1108, 1109, 1109, 1110, 1111, 1111, 1112, 1113, 1113, 1114, 1114, 1115,
    1116, 1116, 1117, 1118, 1118, 1119, 1119, 1120, 1121, 1121, 1122, 1122, 1123, 1124, 1124, 1125,
    1126, 1126, 1127, 1127, 1128, 1129, 1129, 1130, 1131, 1131, 1132, 1132, 1133, 1134, 1134, 1135,
    1135, 1136, 1137, 1137, 1138, 1139, 1139, 1140, 1140, 1141, 1142, 1142, 1143, 1143, 1144, 1145,
    1145, 1146, 1147, 1147, 1148, 1148, 1149, 1150, 1150, 1151, 1152, 1152, 1153, 1153, 1154, 1155,
    1155, 1156, 1156, 1157, 1158, 1158, 1159, 1160, 1160, 1161, 1161, 1162, 1163, 1163, 1164, 1164,
    1165, 1166, 1166, 1167, 1168, 1168, 1169, 1169, 1170, 1171, 1171, 1172, 1173, 1173, 1174, 1174,
    1175, 1176, 1176, 1177, 1177, 1178, 1179, 1179, 1180, 1181, 1181, 1182, 1182, 1183, 1184, 1184,
    1185, 1186, 1186, 1187, 1187, 1188, 1189, 1189, 1190, 1190, 1191, 1192, 1192, 1193, 1194, 1194,
    1195, 1195, 1196, 1197, 1197, 1198, 1198, 1199, 1200, 1200, 1201, 1202, 1202, 1203, 1203, 1204,
    1205, 1205, 1206, 1207, 1207, 1208, 1208, 1209, 1210, 1210, 1211, 1211, 1212, 1213, 1213, 1214,
    1215, 1215, 1216, 1216, 1217, 1218, 1218, 1219, 1219, 1220, 1221, 1221, 1222, 1223, 1223, 1224,
    1224, 1225, 1226, 1226, 1227, 1228, 1228, 1229, 1229, 1230, 1231, 1231, 1232, 1232, 1233, 1234,
    1234, 1235, 1236, 1236, 1237, 1237, 1238, 1239, 1239, 1240, 1241, 1241, 1242, 1242, 1243, 1244,
    1244, 1245, 1245, 1246, 1247, 1247, 1248, 1249, 1249, 1250, 1250, 1251, 1252, 1252, 1253, 1253,
    1254, 1255, 1255, 1256, 1257, 1257, 1258, 1258, 1259, 1260, 1260, 1261, 1262, 1262, 1263, 1263,
    1264, 1265, 1265, 1266, 1266, 1267, 1268, 1268, 1269, 1270, 1270, 1271, 1271, 1272, 1273, 1273,
    1274, 1275, 1275, 1276, 1276, 1277, 1278, 1278, 1279, 1279, 1280, 1281, 1281, 1282, 1283, 1283,
    1284, 1284, 1285, 1286, 1286, 1287, 1287, 1288, 1289, 1289, 1290, 1291, 1291, 1292, 1292, 1293,
    1294, 1294, 1295, 1296, 1296, 1297, 1297, 1298, 1299, 1299, 1300, 1300, 1301, 1302, 1302, 1303,
    1304, 1304, 1305, 1305, 1306, 1307, 1307, 1308, 1308, 1309, 1310, 1310, 1311, 1312, 1312, 1313,
    1313, 1314, 1315, 1315, 1316, 1317, 1317, 1318, 1318, 1319, 1320, 1320, 1321, 1321, 1322, 1323,
    1323, 1324, 1325, 1325, 1326, 1326, 1327, 1328, 1328, 1329, 1330, 1330, 1331, 1331, 1332, 1333,
    1333, 1334, 1334, 1335, 1336, 1336, 1337, 1338, 1338, 1339, 1339, 1340, 1341, 1341, 1342, 1342,
    1343, 1344, 1344, 1345, 1346, 1346, 1347, 1347, 1348, 1349, 1349, 1350, 1351, 1351, 1352, 1352,
    1353, 1354, 1354, 1355, 1355, 1356, 1357, 1357, 1358, 1359, 1359, 1360, 1360, 1361, 1362, 1362,
    1363, 1364, 1364, 1365, 1365, 1366, 1367, 1367, 1368, 1368, 1369, 1370, 1370, 1371, 1372, 1372,
    1373, 1373, 1374, 1375, 1375, 1376, 1376, 1377, 1378, 1378, 1379, 1380, 1380, 1381, 1381, 1382,
    1383, 1383, 1384, 1385, 1385, 1386, 1386, 1387, 1388, 1388, 1389, 1389, 1390, 1391, 1391, 1392,
    1393, 1393, 1394, 1394, 1395, 1396, 1396, 1397, 1397, 1398, 1399, 1399, 1400, 1401, 1401, 1402,
    1402, 1403, 1404, 1404, 1405, 1406, 1406, 1407, 1407, 1408, 1409, 1409, 1410, 1410, 1411, 1412,
    1412, 1413, 1414, 1414, 1415, 1415, 1416, 1417, 1417, 1418, 1419, 1419, 1420, 1420, 1421, 1422,
    1422, 1423, 1423, 1424, 1425, 1425, 1426, 1427, 1427, 1428, 1428, 1429, 1430, 1430, 1431, 1431,
    1432, 1433, 1433, 1434, 1435, 1435, 1436, 1436, 1437, 1438, 1438, 1439, 1440, 1440, 1441, 1441,
    1442, 1443, 1443, 1444, 1444, 1445, 1446, 1446, 1447, 1448, 1448, 1449, 1449, 1450, 1451, 1451,
    1452, 1452, 1453, 1454, 1454, 1455, 1456, 1456, 1457, 1457, 1458, 1459, 1459, 1460, 1461, 1461,
    1462, 1462, 1463, 1464, 1464, 1465, 1465, 1466, 1467, 1467, 1468, 1469, 1469, 1470, 1470, 1471,
    1472, 1472, 1473, 1474, 1474, 1475, 1475, 1476, 1477, 1477, 1478, 1478, 1479, 1480, 1480, 1481,
    1482, 1482, 1483, 1483, 1484, 1485, 1485, 1486, 1486, 1487, 1488, 1488, 1489, 1490, 1490, 1491,
    1491, 1492, 1493, 1493, 1494, 1495, 1495, 1496, 1496, 1497, 1498, 1498, 1499, 1499, 1500, 1501,
    1501, 1502, 1503, 1503, 1504, 1504, 1505, 1506, 1506, 1507, 1508, 1508, 1509, 1509, 1510, 1511,
    1511, 1512, 1512, 1513, 1514, 1514, 1515, 1516, 1516, 1517, 1517, 1518, 1519, 1519, 1520, 1520,
    1521, 1522, 1522, 1523, 1524, 1524, 1525, 1525, 1526, 1527, 1527, 1528, 1529, 1529, 1530, 1530,
    1531, 1532, 1532, 1533, 1533, 1534, 1535, 1535, 1536, 1537, 1537, 1538, 1538, 1539, 1540, 1540,
    1541, 1541, 1542, 1543, 1543, 1544, 1545, 1545, 1546, 1546, 1547, 1548, 1548, 1549, 1550, 1550,
    1551, 1551, 1552, 1553, 1553, 1554, 1554, 1555, 1556, 1556, 1557, 1558, 1558, 1559, 1559, 1560,
    1561, 1561, 1562, 1563, 1563, 1564, 1564, 1565, 1566, 1566, 1567, 1567, 1568, 1569, 1569, 1570,
    1571, 1571, 1572, 1572, 1573, 1574, 1574, 1575, 1575, 1576, 1577, 1577, 1578, 1579, 1579, 1580,
    1580, 1581, 1582, 1582, 1583, 1584, 1584, 1585, 1585, 1586, 1587, 1587, 1588, 1588, 1589, 1590,
    1590, 1591, 1592, 1592, 1593, 1593, 1594, 1595, 1595, 1596, 1596, 1597, 1598, 1598, 1599, 1600,
    1600,
];

/// Theorem 3
/// Quick way to calculate the fibonacci left shift
pub(crate) fn fibonacci_left_shift(n: u64, k: usize) -> u64 {
    //  FIB64[k-1] * n + FIB64[k-2] + FIB_EXT_LEFT_1[n as usize];

    // we need F(-2), F(-1) which are not in the FIB64 array; here;s the workaround
    let (f_km1, f_km2) = match k {
        // Fib[-1], Fib[-2]
        0 => (1, 0),

        // Fib[0], Fib[-1]
        1 => (1, 1),

        // Fib[1], Fib[0]
        2 => (2, 1),

        // anything else
        k => (FIB64[k - 1], FIB64[k - 2]),
    };

    // shifted:
    f_km1 * n + f_km2 * FIB_EXT_LEFT_1[n as usize]
}

/// decodes a fibonacci stream until the very end of the stream
/// there might be a remainder (behind the last 11 delimiter)
/// which is also returned (its value in Fib, and its len in fib)
pub(crate) fn decode_with_remainder<T: BitStore, O: BitOrder>(
    bitstream: &BitSlice<T, O>,
    lastbit_external: bool,
) -> DecodingResult {
    assert!(
        bitstream.len() < 64,
        "fib-codes cant be longer than 64bit, something is wrong!"
    );
    let mut prev_bit = lastbit_external;
    let mut decoded_ints = Vec::new();
    let mut decoded_end_pos: Vec<usize> = Vec::new();

    let mut accum = 0_u64;
    let mut offset = 0;
    for (ix, b) in bitstream.iter().by_vals().enumerate() {
        match (prev_bit, b) {
            (false, true) => {
                accum += FIB64[offset];
                offset += 1;
                prev_bit = b;
            }
            (true, true) => {
                // found delimiter; Note, the bit has already been counted in acc
                decoded_ints.push(accum);
                decoded_end_pos.push(ix); // will be none the first iteration
                // reset for next number
                accum = 0;
                offset = 0;
                // BIG TRICK: we need to set lastbit=false for the next iteration; otherwise 011|11 picks up the next 11 as delimiter
                prev_bit = false;
            }
            (false, false) | (true, false) => {
                // nothing to add, jsut increase offset
                offset += 1;
                prev_bit = b;
            }
        }
    }
    DecodingResult {
        numbers: decoded_ints,
        u: accum,
        lu: offset,
        number_end_in_segment: decoded_end_pos,
    }
}

#[cfg(test)]
mod test_decode_with_remainder {
    use crate::MyBitOrder;

    use super::*;
    use bitvec::{bits, view::BitView};
    use pretty_assertions::assert_eq;
    #[test]
    fn test_decode_with_remainder_edge_case_delimiters() {
        // the exampel from the paper, Fig 9.4
        let bits = bits![u8, MyBitOrder; 0,1,1,1,1];
        let r = decode_with_remainder(bits, false);
        assert_eq!(
            r,
            DecodingResult {
                numbers: vec![2, 1],
                u: 0,
                lu: 0,
                number_end_in_segment: vec![2, 4]
            }
        );
    }

    #[test]
    fn test_decode_with_remainder_edge_case_delimiters2() {
        // the exampel from the paper, Fig 9.4
        let bits = bits![u8, MyBitOrder; 0,0,0,0,0,0,1,1,1,0,0,0,0,0,1,1].to_bitvec();
        let r = decode_with_remainder(&bits, false);
        assert_eq!(
            r,
            DecodingResult {
                numbers: vec![21, 22],
                u: 0,
                lu: 0,
                number_end_in_segment: vec![7, 15]
            }
        );
    }

    #[test]
    fn test_decode_with_remainder_from_table94() {
        // the exampel from the paper, Fig 9.4
        let bits = &181_u8.view_bits::<MyBitOrder>()[..8];
        // bits.reverse();

        // let bits = bits![u8, MyBitOrder; 0,1,1,1,1];
        let r = decode_with_remainder(bits, false);
        assert_eq!(r.numbers, vec![4]);
        assert_eq!(r.u, 7);
        assert_eq!(r.lu, 4);

        // the exampel from the paper, Fig 9.4
        let bits = &165_u8.view_bits::<MyBitOrder>()[..8];
        let r = decode_with_remainder(&bits, true);
        assert_eq!(r.numbers, vec![0]);
        assert_eq!(r.u, 31);
        assert_eq!(r.lu, 7);

        // the exampel from the paper, Fig 9.4
        let bits = &114_u8.view_bits::<MyBitOrder>()[..8];
        let r = decode_with_remainder(&bits, true);
        assert_eq!(r.numbers, vec![2]);
        assert_eq!(r.u, 6);
        assert_eq!(r.lu, 5);
    }

    #[test]
    fn test_decode_with_remainder() {
        // the exampel from the paper, Fig 9.4
        let bits = bits![u8, MyBitOrder; 1,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1];
        let r = decode_with_remainder(bits, false);
        assert_eq!(
            r,
            DecodingResult {
                numbers: vec![4, 7],
                u: 31,
                lu: 7,
                number_end_in_segment: vec![3, 8,]
            }
        );

        // the exampel from the paper, Fig 9.4
        // no remainder this time
        let bits = bits![u8, MyBitOrder; 1,0,1,1,0,1,0,1,1];
        let r = decode_with_remainder(bits, false);
        assert_eq!(
            r,
            DecodingResult {
                numbers: vec![4, 7],
                u: 0,
                lu: 0,
                number_end_in_segment: vec![3, 8]
            }
        );
    }
    #[test]
    fn test_decode_with_remainder_starts() {
        let bits = bits![u8, MyBitOrder; 1,0,1,1,0,1,0,1,1, 0,1,1,0,0,0];
        let r = decode_with_remainder(bits, false);
        assert_eq!(
            r,
            DecodingResult {
                numbers: vec![4, 7, 2],
                u: 0,
                lu: 3,
                number_end_in_segment: vec![3, 8, 11]
            }
        );
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_extended_shift() {
        let x = extended_fibonacci_right_shift_slow(7, 0);
        assert_eq!(x, 7);

        // from table 6.6
        let x = extended_fibonacci_right_shift_slow(7, 1);
        assert_eq!(x, 4);

        let x = extended_fibonacci_right_shift_slow(6, 1);
        assert_eq!(x, 4);

        let x = extended_fibonacci_right_shift_slow(8, 1);
        assert_eq!(x, 5);

        let x = extended_fibonacci_right_shift_slow(9, 1);
        assert_eq!(x, 6);

        let x = extended_fibonacci_right_shift_slow(39, 1);
        assert_eq!(x, 24);

        let x = extended_fibonacci_right_shift_slow(54, 1);
        assert_eq!(x, 33);
    }

    #[test]
    fn test_extended_shift_print() {
        let mut s = String::new();
        s.push_str("0, ");

        for i in 1..2590 {
            let f = extended_fibonacci_right_shift_slow(i, 1);
            let x = format!("{f}, ");
            s.push_str(&x);
        }
        println!("{s}");
    }

    #[test]
    fn test_fib_left() {
        // 32 = 0010101   (3+8+21)
        assert_eq!(fibonacci_left_shift(32, 0), 32);
        assert_eq!(fibonacci_left_shift(32, 3), 136);
    }
}
