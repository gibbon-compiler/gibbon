open GibbonCompat;

datatype dat_Octree = Cell of (int  * int * int * int * int *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree) | Particle of (int  * int * int)| EmptyOct ;

fun maxI (a_302_1416_1872 , b_303_1417_1873) = 
  let val fltIf_1524_1874 = (a_302_1416_1872 > b_303_1417_1873) in 
  (if fltIf_1524_1874 then a_302_1416_1872 
   else b_303_1417_1873) end;

fun momentumOf (t_285_1399_1855) = (case t_285_1399_1855 of Cell (wildcard__106_286_1400_1856 , wildcard__107_287_1401_1857, wildcard__108_288_1402_1858, wildcard__109_289_1403_1859, mom_290_1404_1860, wildcard__110_291_1405_1861, wildcard__111_292_1406_1862, wildcard__112_293_1407_1863, wildcard__113_294_1408_1864, wildcard__114_295_1409_1865, wildcard__115_296_1410_1866, wildcard__116_297_1411_1867, wildcard__117_298_1412_1868) => mom_290_1404_1860 
  | Particle (m_299_1413_1869 , wildcard__131_300_1414_1870, v_301_1415_1871) => (m_299_1413_1869 * v_301_1415_1871)
  | EmptyOct => 0);

fun sum8 (a_239_1353_1741 , b_240_1354_1742, c_241_1355_1743, d_242_1356_1744, e_243_1357_1745, f_244_1358_1746, g_245_1359_1747, h_246_1360_1748) = 
  let val fltPrm_1461_1749 = (a_239_1353_1741 + b_240_1354_1742) in 
  let val fltPrm_1460_1750 = (fltPrm_1461_1749 + c_241_1355_1743) in 
  let val fltPrm_1459_1751 = (fltPrm_1460_1750 + d_242_1356_1744) in 
  let val fltPrm_1458_1752 = (fltPrm_1459_1751 + e_243_1357_1745) in 
  let val fltPrm_1457_1753 = (fltPrm_1458_1752 + f_244_1358_1746) in 
  let val fltPrm_1456_1754 = (fltPrm_1457_1753 + g_245_1359_1747) in (fltPrm_1456_1754 + h_246_1360_1748) end end end end end end;

fun absI (x_238_1352_1739) = 
  let val fltIf_1455_1740 = (x_238_1352_1739 < 0) in 
  (if fltIf_1455_1740 then (0 - x_238_1352_1739) 
   else x_238_1352_1739) end;

fun mixSeed (s_228_1342_1734 , salt_229_1343_1735) = 
  let val fltPrm_1453_1736 = (s_228_1342_1734 * 1103) in 
  let val fltPrm_1454_1737 = (salt_229_1343_1735 * 97) in 
  let val fltPrm_1452_1738 = (fltPrm_1453_1736 + fltPrm_1454_1737) in (fltPrm_1452_1738 + 13) end end end;

fun internal_traverse_Octree (arg_929_1229_1709) = (case arg_929_1229_1709 of Cell (x_930_1230_1710 , x_931_1231_1711, x_932_1232_1712, x_933_1233_1713, x_934_1234_1714, x_935_1235_1715, x_936_1236_1716, x_937_1237_1717, x_938_1238_1718, x_939_1239_1719, x_940_1240_1720, x_941_1241_1721, x_942_1242_1722) => 
  let val y_948_1243_1723 = (internal_traverse_Octree x_935_1235_1715) in 
  let val y_949_1244_1724 = (internal_traverse_Octree x_936_1236_1716) in 
  let val y_950_1245_1725 = (internal_traverse_Octree x_937_1237_1717) in 
  let val y_951_1246_1726 = (internal_traverse_Octree x_938_1238_1718) in 
  let val y_952_1247_1727 = (internal_traverse_Octree x_939_1239_1719) in 
  let val y_953_1248_1728 = (internal_traverse_Octree x_940_1240_1720) in 
  let val y_954_1249_1729 = (internal_traverse_Octree x_941_1241_1721) in 
  let val y_955_1250_1730 = (internal_traverse_Octree x_942_1242_1722) in () end end end end end end end end 
  | Particle (x_956_1251_1731 , x_957_1252_1732, x_958_1253_1733) => ()
  | EmptyOct => ());

fun internal_print_Octree (arg_962_1174_1654) = (case arg_962_1174_1654 of Cell (x_963_1175_1655 , x_964_1176_1656, x_965_1177_1657, x_966_1178_1658, x_967_1179_1659, x_968_1180_1660, x_969_1181_1661, x_970_1182_1662, x_971_1183_1663, x_972_1184_1664, x_973_1185_1665, x_974_1186_1666, x_975_1187_1667) => 
  let val wildcard_989_1188_1668 = (print "(Cell") in 
  let val wildcard_1003_1189_1669 = (print " ") in 
  let val y_976_1190_1670 = (print(Int.toString(x_963_1175_1655))) in 
  let val wildcard_1002_1191_1671 = (print " ") in 
  let val y_977_1192_1672 = (print(Int.toString(x_964_1176_1656))) in 
  let val wildcard_1001_1193_1673 = (print " ") in 
  let val y_978_1194_1674 = (print(Int.toString(x_965_1177_1657))) in 
  let val wildcard_1000_1195_1675 = (print " ") in 
  let val y_979_1196_1676 = (print(Int.toString(x_966_1178_1658))) in 
  let val wildcard_999_1197_1677 = (print " ") in 
  let val y_980_1198_1678 = (print(Int.toString(x_967_1179_1659))) in 
  let val wildcard_998_1199_1679 = (print " ") in 
  let val y_981_1200_1680 = (internal_print_Octree x_968_1180_1660) in 
  let val wildcard_997_1201_1681 = (print " ") in 
  let val y_982_1202_1682 = (internal_print_Octree x_969_1181_1661) in 
  let val wildcard_996_1203_1683 = (print " ") in 
  let val y_983_1204_1684 = (internal_print_Octree x_970_1182_1662) in 
  let val wildcard_995_1205_1685 = (print " ") in 
  let val y_984_1206_1686 = (internal_print_Octree x_971_1183_1663) in 
  let val wildcard_994_1207_1687 = (print " ") in 
  let val y_985_1208_1688 = (internal_print_Octree x_972_1184_1664) in 
  let val wildcard_993_1209_1689 = (print " ") in 
  let val y_986_1210_1690 = (internal_print_Octree x_973_1185_1665) in 
  let val wildcard_992_1211_1691 = (print " ") in 
  let val y_987_1212_1692 = (internal_print_Octree x_974_1186_1666) in 
  let val wildcard_991_1213_1693 = (print " ") in 
  let val y_988_1214_1694 = (internal_print_Octree x_975_1187_1667) in 
  let val wildcard_990_1215_1695 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | Particle (x_1004_1216_1696 , x_1005_1217_1697, x_1006_1218_1698) => 
  let val wildcard_1010_1219_1699 = (print "(Particle") in 
  let val wildcard_1014_1220_1700 = (print " ") in 
  let val y_1007_1221_1701 = (print(Int.toString(x_1004_1216_1696))) in 
  let val wildcard_1013_1222_1702 = (print " ") in 
  let val y_1008_1223_1703 = (print(Int.toString(x_1005_1217_1697))) in 
  let val wildcard_1012_1224_1704 = (print " ") in 
  let val y_1009_1225_1705 = (print(Int.toString(x_1006_1218_1698))) in 
  let val wildcard_1011_1226_1706 = (print ")") in () end end end end end end end end
  | EmptyOct => 
  let val wildcard_1015_1227_1707 = (print "(EmptyOct") in 
  let val wildcard_1016_1228_1708 = (print ")") in () end end);

fun massOf (t_123_1157_1637) = (case t_123_1157_1637 of Cell (m_124_1158_1638 , wildcard__14_125_1159_1639, wildcard__15_126_1160_1640, wildcard__16_127_1161_1641, wildcard__17_128_1162_1642, wildcard__18_129_1163_1643, wildcard__19_130_1164_1644, wildcard__20_131_1165_1645, wildcard__21_132_1166_1646, wildcard__22_133_1167_1647, wildcard__23_134_1168_1648, wildcard__24_135_1169_1649, wildcard__25_136_1170_1650) => m_124_1158_1638 
  | Particle (m_137_1171_1651 , wildcard__39_138_1172_1652, wildcard__40_139_1173_1653) => m_137_1171_1651
  | EmptyOct => 0);

fun weightedPos (t_106_1140_1620) = (case t_106_1140_1620 of Cell (m_107_1141_1621 , c_108_1142_1622, wildcard__45_109_1143_1623, wildcard__46_110_1144_1624, wildcard__47_111_1145_1625, wildcard__48_112_1146_1626, wildcard__49_113_1147_1627, wildcard__50_114_1148_1628, wildcard__51_115_1149_1629, wildcard__52_116_1150_1630, wildcard__53_117_1151_1631, wildcard__54_118_1152_1632, wildcard__55_119_1153_1633) => (m_107_1141_1621 * c_108_1142_1622) 
  | Particle (m_120_1154_1634 , p_121_1155_1635, wildcard__69_122_1156_1636) => (m_120_1154_1634 * p_121_1155_1635)
  | EmptyOct => 0);

fun countActive (t_78_1112_1585 , theta_79_1113_1586) = (case t_78_1112_1585 of Cell (wildcard__223_80_1114_1587 , c_81_1115_1588, wildcard__224_82_1116_1589, s_83_1117_1590, wildcard__225_84_1118_1591, a_85_1119_1592, b_86_1120_1593, c1_87_1121_1594, d_88_1122_1595, e_89_1123_1596, f_90_1124_1597, g_91_1125_1598, h_92_1126_1599) => 
  let val fltAppE_1441_1601 = (c_81_1115_1588 - 0) in 
  let val fltPrm_1440_1602 = (absI fltAppE_1441_1601) in 
  let val dist_94_1128_1603 = (fltPrm_1440_1602 + 1) in 
  let val openLhs_95_1129_1604 = (s_83_1117_1590 * 100) in 
  let val openRhs_96_1130_1605 = (theta_79_1113_1586 * dist_94_1128_1603) in 
  let val fltIf_1442_1606 = (openLhs_95_1129_1604 >= openRhs_96_1130_1605) in 
  let val refine_97_1131_1607 = 
  (if fltIf_1442_1606 then 1 
   else 0) in 
  let val fltAppE_1444_1608 = (countActive(a_85_1119_1592 , theta_79_1113_1586)) in 
  let val fltAppE_1445_1609 = (countActive(b_86_1120_1593 , theta_79_1113_1586)) in 
  let val fltAppE_1446_1610 = (countActive(c1_87_1121_1594 , theta_79_1113_1586)) in 
  let val fltAppE_1447_1611 = (countActive(d_88_1122_1595 , theta_79_1113_1586)) in 
  let val fltAppE_1448_1612 = (countActive(e_89_1123_1596 , theta_79_1113_1586)) in 
  let val fltAppE_1449_1613 = (countActive(f_90_1124_1597 , theta_79_1113_1586)) in 
  let val fltAppE_1450_1614 = (countActive(g_91_1125_1598 , theta_79_1113_1586)) in 
  let val fltAppE_1451_1615 = (countActive(h_92_1126_1599 , theta_79_1113_1586)) in 
  let val fltPrm_1443_1616 = (sum8(fltAppE_1444_1608 , fltAppE_1445_1609, fltAppE_1446_1610, fltAppE_1447_1611, fltAppE_1448_1612, fltAppE_1449_1613, fltAppE_1450_1614, fltAppE_1451_1615)) in (refine_97_1131_1607 + fltPrm_1443_1616) end end end end end end end end end end end end end end end end 
  | Particle (wildcard__244_98_1132_1617 , wildcard__245_99_1133_1618, wildcard__246_100_1134_1619) => 0
  | EmptyOct => 0);

fun countOf (t_44_1078_1568) = (case t_44_1078_1568 of Cell (wildcard__74_45_1079_1569 , wildcard__75_46_1080_1570, n_47_1081_1571, wildcard__76_48_1082_1572, wildcard__77_49_1083_1573, wildcard__78_50_1084_1574, wildcard__79_51_1085_1575, wildcard__80_52_1086_1576, wildcard__81_53_1087_1577, wildcard__82_54_1088_1578, wildcard__83_55_1089_1579, wildcard__84_56_1090_1580, wildcard__85_57_1091_1581) => n_47_1081_1571 
  | Particle (wildcard__99_58_1092_1582 , wildcard__100_59_1093_1583, wildcard__101_60_1094_1584) => 1
  | EmptyOct => 0);

fun buildOctree (d_247_1361_1755 , seed_248_1362_1756, center_249_1363_1757, half_250_1364_1758) = 
  let val fltIf_1462_1759 = (d_247_1361_1755 = 0) in 
  (if fltIf_1462_1759 then 
  let val fltPrm_1464_1760 = (absI seed_248_1362_1756) in 
  let val fltPrm_1463_1761 = (fltPrm_1464_1760 mod 5) in 
  let val m_251_1365_1762 = (1 + fltPrm_1463_1761) in 
  let val fltPrm_1467_1763 = (mixSeed(seed_248_1362_1756 , 3)) in 
  let val fltPrm_1466_1764 = (fltPrm_1467_1763 mod 3) in 
  let val fltPrm_1465_1765 = (center_249_1363_1757 + fltPrm_1466_1764) in 
  let val p_252_1366_1766 = (fltPrm_1465_1765 - 1) in 
  let val fltPrm_1469_1767 = (mixSeed(seed_248_1362_1756 , 11)) in 
  let val fltPrm_1468_1768 = (fltPrm_1469_1767 mod 11) in 
  let val v_253_1367_1769 = (fltPrm_1468_1768 - 5) in (Particle (m_251_1365_1762 , p_252_1366_1766, v_253_1367_1769)) end end end end end end end end end end 
   else 
  let val fltAppE_1470_1770 = (half_250_1364_1758 div 2) in 
  let val half__254_1368_1771 = (maxI(1 , fltAppE_1470_1770)) in 
  let val fltAppE_1471_1772 = (half_250_1364_1758 div 4) in 
  let val stride_255_1369_1773 = (maxI(1 , fltAppE_1471_1772)) in 
  let val fltPrm_1472_1774 = (stride_255_1369_1773 * 7) in 
  let val o0_256_1370_1775 = (0 - fltPrm_1472_1774) in 
  let val fltPrm_1473_1776 = (stride_255_1369_1773 * 5) in 
  let val o1_257_1371_1777 = (0 - fltPrm_1473_1776) in 
  let val fltPrm_1474_1778 = (stride_255_1369_1773 * 3) in 
  let val o2_258_1372_1779 = (0 - fltPrm_1474_1778) in 
  let val o3_259_1373_1780 = (0 - stride_255_1369_1773) in 
  let val o5_261_1375_1782 = (stride_255_1369_1773 * 3) in 
  let val o6_262_1376_1783 = (stride_255_1369_1773 * 5) in 
  let val o7_263_1377_1784 = (stride_255_1369_1773 * 7) in 
  let val fltAppE_1475_1785 = (d_247_1361_1755 - 1) in 
  let val fltAppE_1476_1786 = (mixSeed(seed_248_1362_1756 , 1)) in 
  let val fltAppE_1477_1787 = (center_249_1363_1757 + o0_256_1370_1775) in 
  let val c0_264_1378_1788 = (buildOctree(fltAppE_1475_1785 , fltAppE_1476_1786, fltAppE_1477_1787, half__254_1368_1771)) in 
  let val fltAppE_1478_1789 = (d_247_1361_1755 - 1) in 
  let val fltAppE_1479_1790 = (mixSeed(seed_248_1362_1756 , 2)) in 
  let val fltAppE_1480_1791 = (center_249_1363_1757 + o1_257_1371_1777) in 
  let val c1_265_1379_1792 = (buildOctree(fltAppE_1478_1789 , fltAppE_1479_1790, fltAppE_1480_1791, half__254_1368_1771)) in 
  let val fltAppE_1481_1793 = (d_247_1361_1755 - 1) in 
  let val fltAppE_1482_1794 = (mixSeed(seed_248_1362_1756 , 3)) in 
  let val fltAppE_1483_1795 = (center_249_1363_1757 + o2_258_1372_1779) in 
  let val c2_266_1380_1796 = (buildOctree(fltAppE_1481_1793 , fltAppE_1482_1794, fltAppE_1483_1795, half__254_1368_1771)) in 
  let val fltAppE_1484_1797 = (d_247_1361_1755 - 1) in 
  let val fltAppE_1485_1798 = (mixSeed(seed_248_1362_1756 , 4)) in 
  let val fltAppE_1486_1799 = (center_249_1363_1757 + o3_259_1373_1780) in 
  let val c3_267_1381_1800 = (buildOctree(fltAppE_1484_1797 , fltAppE_1485_1798, fltAppE_1486_1799, half__254_1368_1771)) in 
  let val fltAppE_1487_1801 = (d_247_1361_1755 - 1) in 
  let val fltAppE_1488_1802 = (mixSeed(seed_248_1362_1756 , 5)) in 
  let val fltAppE_1489_1803 = (center_249_1363_1757 + stride_255_1369_1773) in 
  let val c4_268_1382_1804 = (buildOctree(fltAppE_1487_1801 , fltAppE_1488_1802, fltAppE_1489_1803, half__254_1368_1771)) in 
  let val fltAppE_1490_1805 = (d_247_1361_1755 - 1) in 
  let val fltAppE_1491_1806 = (mixSeed(seed_248_1362_1756 , 6)) in 
  let val fltAppE_1492_1807 = (center_249_1363_1757 + o5_261_1375_1782) in 
  let val c5_269_1383_1808 = (buildOctree(fltAppE_1490_1805 , fltAppE_1491_1806, fltAppE_1492_1807, half__254_1368_1771)) in 
  let val fltAppE_1493_1809 = (d_247_1361_1755 - 1) in 
  let val fltAppE_1494_1810 = (mixSeed(seed_248_1362_1756 , 7)) in 
  let val fltAppE_1495_1811 = (center_249_1363_1757 + o6_262_1376_1783) in 
  let val c6_270_1384_1812 = (buildOctree(fltAppE_1493_1809 , fltAppE_1494_1810, fltAppE_1495_1811, half__254_1368_1771)) in 
  let val fltAppE_1496_1813 = (d_247_1361_1755 - 1) in 
  let val fltAppE_1497_1814 = (mixSeed(seed_248_1362_1756 , 8)) in 
  let val fltAppE_1498_1815 = (center_249_1363_1757 + o7_263_1377_1784) in 
  let val c7_271_1385_1816 = (buildOctree(fltAppE_1496_1813 , fltAppE_1497_1814, fltAppE_1498_1815, half__254_1368_1771)) in 
  let val m0_272_1386_1817 = (massOf c0_264_1378_1788) in 
  let val m1_273_1387_1818 = (massOf c1_265_1379_1792) in 
  let val m2_274_1388_1819 = (massOf c2_266_1380_1796) in 
  let val m3_275_1389_1820 = (massOf c3_267_1381_1800) in 
  let val m4_276_1390_1821 = (massOf c4_268_1382_1804) in 
  let val m5_277_1391_1822 = (massOf c5_269_1383_1808) in 
  let val m6_278_1392_1823 = (massOf c6_270_1384_1812) in 
  let val m7_279_1393_1824 = (massOf c7_271_1385_1816) in 
  let val mTot_280_1394_1825 = (sum8(m0_272_1386_1817 , m1_273_1387_1818, m2_274_1388_1819, m3_275_1389_1820, m4_276_1390_1821, m5_277_1391_1822, m6_278_1392_1823, m7_279_1393_1824)) in 
  let val fltAppE_1499_1826 = (weightedPos c0_264_1378_1788) in 
  let val fltAppE_1500_1827 = (weightedPos c1_265_1379_1792) in 
  let val fltAppE_1501_1828 = (weightedPos c2_266_1380_1796) in 
  let val fltAppE_1502_1829 = (weightedPos c3_267_1381_1800) in 
  let val fltAppE_1503_1830 = (weightedPos c4_268_1382_1804) in 
  let val fltAppE_1504_1831 = (weightedPos c5_269_1383_1808) in 
  let val fltAppE_1505_1832 = (weightedPos c6_270_1384_1812) in 
  let val fltAppE_1506_1833 = (weightedPos c7_271_1385_1816) in 
  let val wTot_281_1395_1834 = (sum8(fltAppE_1499_1826 , fltAppE_1500_1827, fltAppE_1501_1828, fltAppE_1502_1829, fltAppE_1503_1830, fltAppE_1504_1831, fltAppE_1505_1832, fltAppE_1506_1833)) in 
  let val fltAppE_1507_1835 = (countOf c0_264_1378_1788) in 
  let val fltAppE_1508_1836 = (countOf c1_265_1379_1792) in 
  let val fltAppE_1509_1837 = (countOf c2_266_1380_1796) in 
  let val fltAppE_1510_1838 = (countOf c3_267_1381_1800) in 
  let val fltAppE_1511_1839 = (countOf c4_268_1382_1804) in 
  let val fltAppE_1512_1840 = (countOf c5_269_1383_1808) in 
  let val fltAppE_1513_1841 = (countOf c6_270_1384_1812) in 
  let val fltAppE_1514_1842 = (countOf c7_271_1385_1816) in 
  let val nTot_282_1396_1843 = (sum8(fltAppE_1507_1835 , fltAppE_1508_1836, fltAppE_1509_1837, fltAppE_1510_1838, fltAppE_1511_1839, fltAppE_1512_1840, fltAppE_1513_1841, fltAppE_1514_1842)) in 
  let val fltAppE_1515_1844 = (momentumOf c0_264_1378_1788) in 
  let val fltAppE_1516_1845 = (momentumOf c1_265_1379_1792) in 
  let val fltAppE_1517_1846 = (momentumOf c2_266_1380_1796) in 
  let val fltAppE_1518_1847 = (momentumOf c3_267_1381_1800) in 
  let val fltAppE_1519_1848 = (momentumOf c4_268_1382_1804) in 
  let val fltAppE_1520_1849 = (momentumOf c5_269_1383_1808) in 
  let val fltAppE_1521_1850 = (momentumOf c6_270_1384_1812) in 
  let val fltAppE_1522_1851 = (momentumOf c7_271_1385_1816) in 
  let val pTot_283_1397_1852 = (sum8(fltAppE_1515_1844 , fltAppE_1516_1845, fltAppE_1517_1846, fltAppE_1518_1847, fltAppE_1519_1848, fltAppE_1520_1849, fltAppE_1521_1850, fltAppE_1522_1851)) in 
  let val fltIf_1523_1853 = (mTot_280_1394_1825 = 0) in 
  let val com_284_1398_1854 = 
  (if fltIf_1523_1853 then center_249_1363_1757 
   else (wTot_281_1395_1834 div mTot_280_1394_1825)) in (Cell (mTot_280_1394_1825 , com_284_1398_1854, nTot_282_1396_1843, half_250_1364_1758, pTot_283_1397_1852, c0_264_1378_1788, c1_265_1379_1792, c2_266_1380_1796, c3_267_1381_1800, c4_268_1382_1804, c5_269_1383_1808, c6_270_1384_1812, c7_271_1385_1816)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end) end;

fun internal_copy_Octree (arg_896_1025_1535) = (case arg_896_1025_1535 of Cell (x_897_1026_1536 , x_898_1027_1537, x_899_1028_1538, x_900_1029_1539, x_901_1030_1540, x_902_1031_1541, x_903_1032_1542, x_904_1033_1543, x_905_1034_1544, x_906_1035_1545, x_907_1036_1546, x_908_1037_1547, x_909_1038_1548) => 
  let val y_915_1044_1554 = (internal_copy_Octree x_902_1031_1541) in 
  let val y_916_1045_1555 = (internal_copy_Octree x_903_1032_1542) in 
  let val y_917_1046_1556 = (internal_copy_Octree x_904_1033_1543) in 
  let val y_918_1047_1557 = (internal_copy_Octree x_905_1034_1544) in 
  let val y_919_1048_1558 = (internal_copy_Octree x_906_1035_1545) in 
  let val y_920_1049_1559 = (internal_copy_Octree x_907_1036_1546) in 
  let val y_921_1050_1560 = (internal_copy_Octree x_908_1037_1547) in 
  let val y_922_1051_1561 = (internal_copy_Octree x_909_1038_1548) in (Cell (x_897_1026_1536 , x_898_1027_1537, x_899_1028_1538, x_900_1029_1539, x_901_1030_1540, y_915_1044_1554, y_916_1045_1555, y_917_1046_1556, y_918_1047_1557, y_919_1048_1558, y_920_1049_1559, y_921_1050_1560, y_922_1051_1561)) end end end end end end end end 
  | Particle (x_923_1052_1562 , x_924_1053_1563, x_925_1054_1564) => (Particle (x_923_1052_1562 , x_924_1053_1563, x_925_1054_1564))
  | EmptyOct => EmptyOct);
val _ = (print(Int.toString(
  let val wildcard__13_16_1017_1525 = (printsym "Running program OctTree Physics Simulation: ") in 
  let val wildcard__11_17_1018_1526 = (printsym "NEWLINE") in 
  let val fltPrm_1439_1527 = 1 in 
  let val fltAppE_1438_1528 = (fltPrm_1439_1527 + 8) in 
  let val octTree_18_1019_1529 = (buildOctree(fltAppE_1438_1528 , 17, 0, 64)) in 
  let val wildcard__8_19_1020_1530 = (printsym "Running pass countActive (fold, uses=10): ") in 
  let val wildcard__6_20_1021_1531 = (printsym "NEWLINE") in 
  let val totActive_21_1022_1532 = (countActive(octTree_18_1019_1529 , 60)) in 
  let val wildcard__2_22_1023_1533 = (printsym "End") in 
  let val wildcard__0_23_1024_1534 = (printsym "NEWLINE") in totActive_21_1022_1532 end end end end end end end end end end)));
val _ = print "\n"
