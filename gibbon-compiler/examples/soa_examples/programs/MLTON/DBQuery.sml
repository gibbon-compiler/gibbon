open GibbonCompat;

datatype dat_Query = Join of (int  * int * int * int *  dat_Query *  dat_Query) | Filter of (int  * int * int * int *  dat_Query)| Scan of (int  * int * int * int)| QEmpty ;

fun internal_traverse_Query (arg_824_1199_1700) = (case arg_824_1199_1700 of Join (x_825_1200_1701 , x_826_1201_1702, x_827_1202_1703, x_828_1203_1704, x_829_1204_1705, x_830_1205_1706) => 
  let val y_835_1206_1707 = (internal_traverse_Query x_829_1204_1705) in 
  let val y_836_1207_1708 = (internal_traverse_Query x_830_1205_1706) in () end end 
  | Filter (x_837_1208_1709 , x_838_1209_1710, x_839_1210_1711, x_840_1211_1712, x_841_1212_1713) => 
  let val y_846_1213_1714 = (internal_traverse_Query x_841_1212_1713) in () end
  | Scan (x_847_1214_1715 , x_848_1215_1716, x_849_1216_1717, x_850_1217_1718) => ()
  | QEmpty => ());

fun internal_print_Query (arg_855_1145_1646) = (case arg_855_1145_1646 of Join (x_856_1146_1647 , x_857_1147_1648, x_858_1148_1649, x_859_1149_1650, x_860_1150_1651, x_861_1151_1652) => 
  let val wildcard_868_1152_1653 = (print "(Join") in 
  let val wildcard_875_1153_1654 = (print " ") in 
  let val y_862_1154_1655 = (print(Int.toString(x_856_1146_1647))) in 
  let val wildcard_874_1155_1656 = (print " ") in 
  let val y_863_1156_1657 = (print(Int.toString(x_857_1147_1648))) in 
  let val wildcard_873_1157_1658 = (print " ") in 
  let val y_864_1158_1659 = (print(Int.toString(x_858_1148_1649))) in 
  let val wildcard_872_1159_1660 = (print " ") in 
  let val y_865_1160_1661 = (print(Int.toString(x_859_1149_1650))) in 
  let val wildcard_871_1161_1662 = (print " ") in 
  let val y_866_1162_1663 = (internal_print_Query x_860_1150_1651) in 
  let val wildcard_870_1163_1664 = (print " ") in 
  let val y_867_1164_1665 = (internal_print_Query x_861_1151_1652) in 
  let val wildcard_869_1165_1666 = (print ")") in () end end end end end end end end end end end end end end 
  | Filter (x_876_1166_1667 , x_877_1167_1668, x_878_1168_1669, x_879_1169_1670, x_880_1170_1671) => 
  let val wildcard_886_1171_1672 = (print "(Filter") in 
  let val wildcard_892_1172_1673 = (print " ") in 
  let val y_881_1173_1674 = (print(Int.toString(x_876_1166_1667))) in 
  let val wildcard_891_1174_1675 = (print " ") in 
  let val y_882_1175_1676 = (print(Int.toString(x_877_1167_1668))) in 
  let val wildcard_890_1176_1677 = (print " ") in 
  let val y_883_1177_1678 = (print(Int.toString(x_878_1168_1669))) in 
  let val wildcard_889_1178_1679 = (print " ") in 
  let val y_884_1179_1680 = (print(Int.toString(x_879_1169_1670))) in 
  let val wildcard_888_1180_1681 = (print " ") in 
  let val y_885_1181_1682 = (internal_print_Query x_880_1170_1671) in 
  let val wildcard_887_1182_1683 = (print ")") in () end end end end end end end end end end end end
  | Scan (x_893_1183_1684 , x_894_1184_1685, x_895_1185_1686, x_896_1186_1687) => 
  let val wildcard_901_1187_1688 = (print "(Scan") in 
  let val wildcard_906_1188_1689 = (print " ") in 
  let val y_897_1189_1690 = (print(Int.toString(x_893_1183_1684))) in 
  let val wildcard_905_1190_1691 = (print " ") in 
  let val y_898_1191_1692 = (print(Int.toString(x_894_1184_1685))) in 
  let val wildcard_904_1192_1693 = (print " ") in 
  let val y_899_1193_1694 = (print(Int.toString(x_895_1185_1686))) in 
  let val wildcard_903_1194_1695 = (print " ") in 
  let val y_900_1195_1696 = (print(Int.toString(x_896_1186_1687))) in 
  let val wildcard_902_1196_1697 = (print ")") in () end end end end end end end end end end
  | QEmpty => 
  let val wildcard_907_1197_1698 = (print "(QEmpty") in 
  let val wildcard_908_1198_1699 = (print ")") in () end end);

fun absI (x_485_1105_1545) = 
  let val fltIf_1253_1546 = (x_485_1105_1545 < 0) in 
  (if fltIf_1253_1546 then (0 - x_485_1105_1545) 
   else x_485_1105_1545) end;

fun filterSelectivitySkew (q_486_1106_1547) = (case q_486_1106_1547 of Filter (wildcard__164_487_1107_1548 , sel_488_1108_1549, wildcard__165_489_1109_1550, wildcard__166_490_1110_1551, s_491_1111_1552) => 
  let val fltAppE_1255_1553 = (sel_488_1108_1549 - 500) in 
  let val fltPrm_1254_1554 = (absI fltAppE_1255_1553) in 
  let val fltPrm_1256_1555 = (filterSelectivitySkew s_491_1111_1552) in (fltPrm_1254_1554 + fltPrm_1256_1555) end end end 
  | Join (wildcard__172_492_1112_1556 , wildcard__173_493_1113_1557, wildcard__174_494_1114_1558, wildcard__175_495_1115_1559, l_496_1116_1560, r_497_1117_1561) => 
  let val fltPrm_1257_1562 = (filterSelectivitySkew l_496_1116_1560) in 
  let val fltPrm_1258_1563 = (filterSelectivitySkew r_497_1117_1561) in (fltPrm_1257_1562 + fltPrm_1258_1563) end end
  | Scan (wildcard__182_498_1118_1564 , wildcard__183_499_1119_1565, wildcard__184_500_1120_1566, wildcard__185_501_1121_1567) => 0
  | QEmpty => 0);

fun hashJoinPressure (q_468_1088_1524) = (case q_468_1088_1524 of Join (jt_469_1089_1525 , wildcard__137_470_1090_1526, wildcard__138_471_1091_1527, m_472_1092_1528, l_473_1093_1529, r_474_1094_1530) => 
  let val fltIf_1249_1531 = (jt_469_1089_1525 = 1) in 
  let val mine_475_1095_1532 = 
  (if fltIf_1249_1531 then m_472_1092_1528 
   else 0) in 
  let val fltPrm_1251_1533 = (hashJoinPressure l_473_1093_1529) in 
  let val fltPrm_1250_1534 = (mine_475_1095_1532 + fltPrm_1251_1533) in 
  let val fltPrm_1252_1535 = (hashJoinPressure r_474_1094_1530) in (fltPrm_1250_1534 + fltPrm_1252_1535) end end end end end 
  | Filter (wildcard__146_476_1096_1536 , wildcard__147_477_1097_1537, wildcard__148_478_1098_1538, wildcard__149_479_1099_1539, s_480_1100_1540) => (hashJoinPressure s_480_1100_1540)
  | Scan (wildcard__155_481_1101_1541 , wildcard__156_482_1102_1542, wildcard__157_483_1103_1543, wildcard__158_484_1104_1544) => 0
  | QEmpty => 0);

fun scaleCosts (q_451_1071_1501 , k_452_1072_1502) = (case q_451_1071_1501 of Join (t_453_1073_1503 , r_454_1074_1504, c_455_1075_1505, m_456_1076_1506, l_457_1077_1507, s_458_1078_1508) => 
  let val fltPkd_1243_1509 = (c_455_1075_1505 * k_452_1072_1502) in 
  let val fltPkd_1244_1510 = (scaleCosts(l_457_1077_1507 , k_452_1072_1502)) in 
  let val fltPkd_1245_1511 = (scaleCosts(s_458_1078_1508 , k_452_1072_1502)) in (Join (t_453_1073_1503 , r_454_1074_1504, fltPkd_1243_1509, m_456_1076_1506, fltPkd_1244_1510, fltPkd_1245_1511)) end end end 
  | Filter (p_459_1079_1512 , sel_460_1080_1513, c_461_1081_1514, f_462_1082_1515, s_463_1083_1516) => 
  let val fltPkd_1246_1517 = (c_461_1081_1514 * k_452_1072_1502) in 
  let val fltPkd_1247_1518 = (scaleCosts(s_463_1083_1516 , k_452_1072_1502)) in (Filter (p_459_1079_1512 , sel_460_1080_1513, fltPkd_1246_1517, f_462_1082_1515, fltPkd_1247_1518)) end end
  | Scan (t_464_1084_1519 , r_465_1085_1520, c_466_1086_1521, w_467_1087_1522) => 
  let val fltPkd_1248_1523 = (c_466_1086_1521 * k_452_1072_1502) in (Scan (t_464_1084_1519 , r_465_1085_1520, fltPkd_1248_1523, w_467_1087_1522)) end
  | QEmpty => QEmpty);

fun mixSeed (s_449_1069_1496 , salt_450_1070_1497) =
  let
    val ws = Word64.fromInt s_449_1069_1496
    val w = Word64.+ (Word64.* (ws, 0w1103 : Word64.word),
                      Word64.+ (Word64.* (Word64.fromInt salt_450_1070_1497, 0w97 : Word64.word), 0w13 : Word64.word))
    val w32 = Word32.fromLarge (Word64.toLarge w)
  in
    Word32.toIntX w32
  end;

fun clearQueryFlags (q_433_1053_1477) = (case q_433_1053_1477 of Filter (p_434_1054_1478 , sel_435_1055_1479, c_436_1056_1480, wildcard__212_437_1057_1481, sub_438_1058_1482) => 
  let val fltPkd_1237_1483 = (clearQueryFlags sub_438_1058_1482) in (Filter (p_434_1054_1478 , sel_435_1055_1479, c_436_1056_1480, 0, fltPkd_1237_1483)) end 
  | Join (t_439_1059_1484 , r_440_1060_1485, c_441_1061_1486, m_442_1062_1487, l_443_1063_1488, s_444_1064_1489) => 
  let val fltPkd_1238_1490 = (clearQueryFlags l_443_1063_1488) in 
  let val fltPkd_1239_1491 = (clearQueryFlags s_444_1064_1489) in (Join (t_439_1059_1484 , r_440_1060_1485, c_441_1061_1486, m_442_1062_1487, fltPkd_1238_1490, fltPkd_1239_1491)) end end
  | Scan (t_445_1065_1492 , r_446_1066_1493, c_447_1067_1494, w_448_1068_1495) => (Scan (t_445_1065_1492 , r_446_1066_1493, c_447_1067_1494, w_448_1068_1495))
  | QEmpty => QEmpty);

fun internal_copy_Query (arg_793_1022_1446) = (case arg_793_1022_1446 of Join (x_794_1023_1447 , x_795_1024_1448, x_796_1025_1449, x_797_1026_1450, x_798_1027_1451, x_799_1028_1452) => 
  let val y_804_1033_1457 = (internal_copy_Query x_798_1027_1451) in 
  let val y_805_1034_1458 = (internal_copy_Query x_799_1028_1452) in (Join (x_794_1023_1447 , x_795_1024_1448, x_796_1025_1449, x_797_1026_1450, y_804_1033_1457, y_805_1034_1458)) end end 
  | Filter (x_806_1035_1459 , x_807_1036_1460, x_808_1037_1461, x_809_1038_1462, x_810_1039_1463) => 
  let val y_815_1044_1468 = (internal_copy_Query x_810_1039_1463) in (Filter (x_806_1035_1459 , x_807_1036_1460, x_808_1037_1461, x_809_1038_1462, y_815_1044_1468)) end
  | Scan (x_816_1045_1469 , x_817_1046_1470, x_818_1047_1471, x_819_1048_1472) => (Scan (x_816_1045_1469 , x_817_1046_1470, x_818_1047_1471, x_819_1048_1472))
  | QEmpty => QEmpty);

fun sumMemory (q_417_1006_1426) = (case q_417_1006_1426 of Join (wildcard__112_418_1007_1427 , wildcard__113_419_1008_1428, wildcard__114_420_1009_1429, m_421_1010_1430, l_422_1011_1431, r_423_1012_1432) => 
  let val fltPrm_1234_1433 = (sumMemory l_422_1011_1431) in 
  let val fltPrm_1233_1434 = (m_421_1010_1430 + fltPrm_1234_1433) in 
  let val fltPrm_1235_1435 = (sumMemory r_423_1012_1432) in (fltPrm_1233_1434 + fltPrm_1235_1435) end end end 
  | Filter (wildcard__121_424_1013_1436 , wildcard__122_425_1014_1437, c_426_1015_1438, wildcard__123_427_1016_1439, s_428_1017_1440) => 
  let val fltPrm_1236_1441 = (sumMemory s_428_1017_1440) in (c_426_1015_1438 + fltPrm_1236_1441) end
  | Scan (wildcard__129_429_1018_1442 , wildcard__130_430_1019_1443, wildcard__131_431_1020_1444, w_432_1021_1445) => w_432_1021_1445
  | QEmpty => 0);

fun maxI (a_397_986_1400 , b_398_987_1401) = 
  let val fltIf_1227_1402 = (a_397_986_1400 > b_398_987_1401) in 
  (if fltIf_1227_1402 then a_397_986_1400 
   else b_398_987_1401) end;

fun sumRows (q_399_988_1403) = (case q_399_988_1403 of Join (wildcard__57_400_989_1404 , r_401_990_1405, wildcard__58_402_991_1406, wildcard__59_403_992_1407, l_404_993_1408, s_405_994_1409) => 
  let val fltPrm_1229_1410 = (sumRows l_404_993_1408) in 
  let val fltPrm_1228_1411 = (r_401_990_1405 + fltPrm_1229_1410) in 
  let val fltPrm_1230_1412 = (sumRows s_405_994_1409) in (fltPrm_1228_1411 + fltPrm_1230_1412) end end end 
  | Filter (wildcard__66_406_995_1413 , sel_407_996_1414, wildcard__67_408_997_1415, wildcard__68_409_998_1416, s_410_999_1417) => 
  let val childRows_411_1000_1418 = (sumRows s_410_999_1417) in 
  let
    val a = childRows_411_1000_1418
    val b = sel_407_996_1414
    val wa32 = Word32.fromInt(if a < 0 then ~a else a)
    val wb32 = Word32.fromInt(if b < 0 then ~b else b)
    val wp = Word32.* (wa32, wb32)
    val prod = Word32.toIntX wp
    val fltPrm_1232_1419 = (prod * (if (a < 0) = (b < 0) then 1 else ~1)) div 1000
  in 
  let val fltAppE_1231_1420 = (fltPrm_1232_1419 div 1000) in 
  let val outRows_412_1001_1421 = (maxI(1 , fltAppE_1231_1420)) in (outRows_412_1001_1421 + childRows_411_1000_1418) end end end end
  | Scan (wildcard__76_413_1002_1422 , r_414_1003_1423, wildcard__77_415_1004_1424, wildcard__78_416_1005_1425) => r_414_1003_1423
  | QEmpty => 0);

fun buildQuery (d_502_1122_1568 , seed_503_1123_1569) = 
  let val fltIf_1259_1570 = (d_502_1122_1568 = 0) in 
  (if fltIf_1259_1570 then 
  let val fltPrm_1260_1571 = (absI seed_503_1123_1569) in 
  let val tableId_504_1124_1572 = (fltPrm_1260_1571 mod 17) in 
  let val fltAppE_1263_1573 = (mixSeed(seed_503_1123_1569 , 3)) in 
  let val fltPrm_1262_1574 = (absI fltAppE_1263_1573) in 
  let val fltPrm_1261_1575 = (fltPrm_1262_1574 mod 6000) in 
  let val rows_505_1125_1576 = (2000 + fltPrm_1261_1575) in 
  let val fltPrm_1264_1577 = (rows_505_1125_1576 div 16) in 
  let val cost_506_1126_1578 = (20 + fltPrm_1264_1577) in 
  let val fltAppE_1267_1579 = (mixSeed(seed_503_1123_1569 , 7)) in 
  let val fltPrm_1266_1580 = (absI fltAppE_1267_1579) in 
  let val fltPrm_1265_1581 = (fltPrm_1266_1580 mod 120) in 
  let val width_507_1127_1582 = (24 + fltPrm_1265_1581) in (Scan (tableId_504_1124_1572 , rows_505_1125_1576, cost_506_1126_1578, width_507_1127_1582)) end end end end end end end end end end end end 
   else 
  let val fltAppE_1269_1583 = (mixSeed(seed_503_1123_1569 , 11)) in 
  let val fltPrm_1268_1584 = (absI fltAppE_1269_1583) in 
  let val tag_508_1128_1585 = (fltPrm_1268_1584 mod 4) in 
  let val fltIf_1270_1586 = (tag_508_1128_1585 < 2) in 
  (if fltIf_1270_1586 then 
  let val fltAppE_1271_1587 = (d_502_1122_1568 - 1) in 
  let val fltAppE_1272_1588 = (mixSeed(seed_503_1123_1569 , 1)) in 
  let val l_509_1129_1589 = (buildQuery(fltAppE_1271_1587 , fltAppE_1272_1588)) in 
  let val fltIf_1273_1590 = (d_502_1122_1568 > 1) in 
  let val rDepth_510_1130_1591 = 
  (if fltIf_1273_1590 then (d_502_1122_1568 - 2) 
   else 0) in 
  let val fltAppE_1274_1592 = (mixSeed(seed_503_1123_1569 , 2)) in 
  let val r_511_1131_1593 = (buildQuery(rDepth_510_1130_1591 , fltAppE_1274_1592)) in 
  let val fltAppE_1276_1594 = (mixSeed(seed_503_1123_1569 , 13)) in 
  let val fltPrm_1275_1595 = (absI fltAppE_1276_1594) in 
  let val joinTy_512_1132_1596 = (fltPrm_1275_1595 mod 3) in 
  let val fltPrm_1278_1597 = (d_502_1122_1568 * 220) in 
  let val fltPrm_1277_1598 = (1200 + fltPrm_1278_1597) in 
  let val fltAppE_1281_1599 = (mixSeed(seed_503_1123_1569 , 17)) in 
  let val fltPrm_1280_1600 = (absI fltAppE_1281_1599) in 
  let val fltPrm_1279_1601 = (fltPrm_1280_1600 mod 2000) in 
  let val lRows_513_1133_1602 = (fltPrm_1277_1598 + fltPrm_1279_1601) in 
  let val fltPrm_1283_1603 = (d_502_1122_1568 * 170) in 
  let val fltPrm_1282_1604 = (1000 + fltPrm_1283_1603) in 
  let val fltAppE_1286_1605 = (mixSeed(seed_503_1123_1569 , 19)) in 
  let val fltPrm_1285_1606 = (absI fltAppE_1286_1605) in 
  let val fltPrm_1284_1607 = (fltPrm_1285_1606 mod 1700) in 
  let val rRows_514_1134_1608 = (fltPrm_1282_1604 + fltPrm_1284_1607) in 
  let val fltAppE_1289_1609 = (mixSeed(seed_503_1123_1569 , 23)) in 
  let val fltPrm_1288_1610 = (absI fltAppE_1289_1609) in 
  let val fltPrm_1287_1611 = (fltPrm_1288_1610 mod 260) in 
  let val sel_515_1135_1612 = (60 + fltPrm_1287_1611) in 
  let val fltPrm_1291_1613 = (lRows_513_1133_1602 * rRows_514_1134_1608) in 
  let val fltPrm_1293_1614 = (sel_515_1135_1612 * 10) in 
  let val fltPrm_1292_1615 = (fltPrm_1293_1614 + 1) in 
  let val fltAppE_1290_1616 = (fltPrm_1291_1613 div fltPrm_1292_1615) in 
  let val outRows_516_1136_1617 = (maxI(1 , fltAppE_1290_1616)) in 
  let val fltIf_1294_1618 = (joinTy_512_1132_1596 = 0) in 
  let val joinCpu_517_1137_1623 = 
  (if fltIf_1294_1618 then 
  let val fltPrm_1295_1619 = (lRows_513_1133_1602 * rRows_514_1134_1608) in (fltPrm_1295_1619 div 2400) end 
   else 
  let val fltIf_1296_1620 = (joinTy_512_1132_1596 = 1) in 
  (if fltIf_1296_1620 then 
  let val fltPrm_1297_1621 = (lRows_513_1133_1602 + rRows_514_1134_1608) in (fltPrm_1297_1621 div 7) end 
   else 
  let val fltPrm_1298_1622 = (lRows_513_1133_1602 + rRows_514_1134_1608) in (fltPrm_1298_1622 div 9) end) end) in 
  let val fltPrm_1299_1624 = (30 + joinCpu_517_1137_1623) in 
  let val fltPrm_1300_1625 = (outRows_516_1136_1617 div 20) in 
  let val total_518_1138_1626 = (fltPrm_1299_1624 + fltPrm_1300_1625) in 
  let val fltIf_1301_1627 = (joinTy_512_1132_1596 = 1) in 
  let val mem_519_1139_1628 = 
  (if fltIf_1301_1627 then (rRows_514_1134_1608 div 2) 
   else (outRows_516_1136_1617 div 8)) in (Join (joinTy_512_1132_1596 , outRows_516_1136_1617, total_518_1138_1626, mem_519_1139_1628, l_509_1129_1589, r_511_1131_1593)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
   else 
  let val fltAppE_1302_1629 = (d_502_1122_1568 - 1) in 
  let val fltAppE_1303_1630 = (mixSeed(seed_503_1123_1569 , 3)) in 
  let val s_520_1140_1631 = (buildQuery(fltAppE_1302_1629 , fltAppE_1303_1630)) in 
  let val fltAppE_1305_1632 = (mixSeed(seed_503_1123_1569 , 29)) in 
  let val fltPrm_1304_1633 = (absI fltAppE_1305_1632) in 
  let val predId_521_1141_1634 = (fltPrm_1304_1633 mod 31) in 
  let val fltAppE_1308_1635 = (mixSeed(seed_503_1123_1569 , 31)) in 
  let val fltPrm_1307_1636 = (absI fltAppE_1308_1635) in 
  let val fltPrm_1306_1637 = (fltPrm_1307_1636 mod 760) in 
  let val sel_522_1142_1638 = (120 + fltPrm_1306_1637) in 
  let val fltAppE_1311_1639 = (mixSeed(seed_503_1123_1569 , 37)) in 
  let val fltPrm_1310_1640 = (absI fltAppE_1311_1639) in 
  let val fltPrm_1309_1641 = (fltPrm_1310_1640 mod 40) in 
  let val cpu_523_1143_1642 = (4 + fltPrm_1309_1641) in 
  let val fltAppE_1313_1643 = (mixSeed(seed_503_1123_1569 , 41)) in 
  let val fltPrm_1312_1644 = (absI fltAppE_1313_1643) in 
  let val flags_524_1144_1645 = (fltPrm_1312_1644 mod 8) in (Filter (predId_521_1141_1634 , sel_522_1142_1638, cpu_523_1143_1642, flags_524_1144_1645, s_520_1140_1631)) end end end end end end end end end end end end end end end end end) end end end end) end;

fun countJoins (q_381_970_1381) = (case q_381_970_1381 of Join (wildcard__84_382_971_1382 , wildcard__85_383_972_1383, wildcard__86_384_973_1384, wildcard__87_385_974_1385, l_386_975_1386, r_387_976_1387) => 
  let val fltPrm_1225_1388 = (countJoins l_386_975_1386) in 
  let val fltPrm_1224_1389 = (1 + fltPrm_1225_1388) in 
  let val fltPrm_1226_1390 = (countJoins r_387_976_1387) in (fltPrm_1224_1389 + fltPrm_1226_1390) end end end 
  | Filter (wildcard__94_388_977_1391 , wildcard__95_389_978_1392, wildcard__96_390_979_1393, wildcard__97_391_980_1394, s_392_981_1395) => (countJoins s_392_981_1395)
  | Scan (wildcard__103_393_982_1396 , wildcard__104_394_983_1397, wildcard__105_395_984_1398, wildcard__106_396_985_1399) => 0
  | QEmpty => 0);

fun sumCost (q_365_954_1361) = (case q_365_954_1361 of Join (wildcard__32_366_955_1362 , wildcard__33_367_956_1363, c_368_957_1364, wildcard__34_369_958_1365, l_370_959_1366, r_371_960_1367) => 
  let val fltPrm_1221_1368 = (sumCost l_370_959_1366) in 
  let val fltPrm_1220_1369 = (c_368_957_1364 + fltPrm_1221_1368) in 
  let val fltPrm_1222_1370 = (sumCost r_371_960_1367) in (fltPrm_1220_1369 + fltPrm_1222_1370) end end end 
  | Filter (wildcard__41_372_961_1371 , wildcard__42_373_962_1372, c_374_963_1373, wildcard__43_375_964_1374, s_376_965_1375) => 
  let val fltPrm_1223_1376 = (sumCost s_376_965_1375) in (c_374_963_1373 + fltPrm_1223_1376) end
  | Scan (wildcard__49_377_966_1377 , wildcard__50_378_967_1378, c_379_968_1379, wildcard__51_380_969_1380) => c_379_968_1379
  | QEmpty => 0);
val _ = (case 
  let val wildcard__317_320_909_1314 = (print "Running Data base Query Pass: ") in 
  let val wildcard__315_321_910_1315 = (printsym "NEWLINE") in 
  let val fltPrm_1219_1316 = (GibbonCompat.getSizeParam()) in 
  let val fltAppE_1218_1317 = (fltPrm_1219_1316 + 10) in 
  let val queryTree_322_911_1318 = (buildQuery(fltAppE_1218_1317 , 17)) in 
  let val wildcard__312_323_912_1319 = (print "Running pass sumCost (fold, uses=6): ") in 
  let val wildcard__310_324_913_1320 = (printsym "NEWLINE") in 
  let val totCost_325_914_1321 = (sumCost queryTree_322_911_1318) in 
  let val wildcard__306_326_915_1322 = (print "End") in 
  let val wildcard__304_327_916_1323 = (printsym "NEWLINE") in 
  let val wildcard__302_328_917_1324 = (print "Running pass sumRows (fold, uses=6): ") in 
  let val wildcard__300_329_918_1325 = (printsym "NEWLINE") in 
  let val totRows_330_919_1326 = (sumRows queryTree_322_911_1318) in 
  let val wildcard__296_331_920_1327 = (print "End") in 
  let val wildcard__294_332_921_1328 = (printsym "NEWLINE") in 
  let val wildcard__292_333_922_1329 = (print "Running pass countJoins (fold, uses=3): ") in 
  let val wildcard__290_334_923_1330 = (printsym "NEWLINE") in 
  let val totJoins_335_924_1331 = (countJoins queryTree_322_911_1318) in 
  let val wildcard__286_336_925_1332 = (print "End") in 
  let val wildcard__284_337_926_1333 = (printsym "NEWLINE") in 
  let val wildcard__282_338_927_1334 = (print "Running pass sumMemory (fold, uses=6): ") in 
  let val wildcard__280_339_928_1335 = (printsym "NEWLINE") in 
  let val totMem_340_929_1336 = (sumMemory queryTree_322_911_1318) in 
  let val wildcard__276_341_930_1337 = (print "End") in 
  let val wildcard__274_342_931_1338 = (printsym "NEWLINE") in 
  let val wildcard__272_343_932_1339 = (print "Running pass hashJoinPressure (fold, uses=5): ") in 
  let val wildcard__270_344_933_1340 = (printsym "NEWLINE") in 
  let val hashPressure_345_934_1341 = (hashJoinPressure queryTree_322_911_1318) in 
  let val wildcard__266_346_935_1342 = (print "End") in 
  let val wildcard__264_347_936_1343 = (printsym "NEWLINE") in 
  let val wildcard__262_348_937_1344 = (print "Running pass filterSelectivitySkew (fold, uses=5): ") in 
  let val wildcard__260_349_938_1345 = (printsym "NEWLINE") in 
  let val selSkew_350_939_1346 = (filterSelectivitySkew queryTree_322_911_1318) in 
  let val wildcard__256_351_940_1347 = (print "End") in 
  let val wildcard__254_352_941_1348 = (printsym "NEWLINE") in 
  let val wildcard__252_353_942_1349 = (print "Running pass scaleCosts (map, uses=15): ") in 
  let val wildcard__250_354_943_1350 = (printsym "NEWLINE") in 
  let val queryTree__355_944_1351 = (scaleCosts(queryTree_322_911_1318 , 10)) in 
  let val wildcard__246_356_945_1352 = (print "End") in 
  let val wildcard__244_357_946_1353 = (printsym "NEWLINE") in 
  let val wildcard__242_358_947_1354 = (print "Running pass clearQueryFlags (map, uses=14): ") in 
  let val wildcard__240_359_948_1355 = (printsym "NEWLINE") in 
  let val queryTree___360_949_1356 = (clearQueryFlags queryTree__355_944_1351) in 
  let val wildcard__236_361_950_1357 = (print "End") in 
  let val wildcard__234_362_951_1358 = (printsym "NEWLINE") in 
  let val mapCost1_363_952_1359 = (sumCost queryTree__355_944_1351) in 
  let val mapCost2_364_953_1360 = (sumCost queryTree___360_949_1356) in (totCost_325_914_1321 , totRows_330_919_1326, totJoins_335_924_1331, totMem_340_929_1336, hashPressure_345_934_1341, selSkew_350_939_1346, mapCost1_363_952_1359, mapCost2_364_953_1360) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3, x__4, x__5, x__6, x__7, x__8) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print " "val _ = (print(Int.toString(x__4))) val _ = print " "val _ = (print(Int.toString(x__5))) val _ = print " "val _ = (print(Int.toString(x__6))) val _ = print " "val _ = (print(Int.toString(x__7))) val _ = print " "val _ = (print(Int.toString(x__8))) val _ = print ")" in () end);
val _ = print "\n"
