datatype dat_Octree = Cell of (int  * int * int * int * int *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree) | Particle of (int  * int * int)| EmptyOct ;

fun maxI (a_302_1416_1858 , b_303_1417_1859) = 
  let val fltIf_1520_1860 = (a_302_1416_1858 > b_303_1417_1859) in 
  (if fltIf_1520_1860 then a_302_1416_1858 
   else b_303_1417_1859) end;

fun momentumOf (t_285_1399_1841) = (case t_285_1399_1841 of Cell (wildcard__106_286_1400_1842 , wildcard__107_287_1401_1843, wildcard__108_288_1402_1844, wildcard__109_289_1403_1845, mom_290_1404_1846, wildcard__110_291_1405_1847, wildcard__111_292_1406_1848, wildcard__112_293_1407_1849, wildcard__113_294_1408_1850, wildcard__114_295_1409_1851, wildcard__115_296_1410_1852, wildcard__116_297_1411_1853, wildcard__117_298_1412_1854) => mom_290_1404_1846 
  | Particle (m_299_1413_1855 , wildcard__131_300_1414_1856, v_301_1415_1857) => (m_299_1413_1855 * v_301_1415_1857)
  | EmptyOct => 0);

fun sum8 (a_239_1353_1727 , b_240_1354_1728, c_241_1355_1729, d_242_1356_1730, e_243_1357_1731, f_244_1358_1732, g_245_1359_1733, h_246_1360_1734) = 
  let val fltPrm_1457_1735 = (a_239_1353_1727 + b_240_1354_1728) in 
  let val fltPrm_1456_1736 = (fltPrm_1457_1735 + c_241_1355_1729) in 
  let val fltPrm_1455_1737 = (fltPrm_1456_1736 + d_242_1356_1730) in 
  let val fltPrm_1454_1738 = (fltPrm_1455_1737 + e_243_1357_1731) in 
  let val fltPrm_1453_1739 = (fltPrm_1454_1738 + f_244_1358_1732) in 
  let val fltPrm_1452_1740 = (fltPrm_1453_1739 + g_245_1359_1733) in (fltPrm_1452_1740 + h_246_1360_1734) end end end end end end;

fun absI (x_238_1352_1725) = 
  let val fltIf_1451_1726 = (x_238_1352_1725 < 0) in 
  (if fltIf_1451_1726 then (0 - x_238_1352_1725) 
   else x_238_1352_1725) end;

fun mixSeed (s_228_1342_1720 , salt_229_1343_1721) = 
  let val fltPrm_1449_1722 = (s_228_1342_1720 * 1103) in 
  let val fltPrm_1450_1723 = (salt_229_1343_1721 * 97) in 
  let val fltPrm_1448_1724 = (fltPrm_1449_1722 + fltPrm_1450_1723) in (fltPrm_1448_1724 + 13) end end end;

fun sumMass (t_186_1300_1695) = (case t_186_1300_1695 of Cell (wildcard__176_187_1301_1696 , wildcard__177_188_1302_1697, wildcard__178_189_1303_1698, wildcard__179_190_1304_1699, wildcard__180_191_1305_1700, a_192_1306_1701, b_193_1307_1702, c_194_1308_1703, d_195_1309_1704, e_196_1310_1705, f_197_1311_1706, g_198_1312_1707, h_199_1313_1708) => 
  let val fltAppE_1440_1709 = (sumMass a_192_1306_1701) in 
  let val fltAppE_1441_1710 = (sumMass b_193_1307_1702) in 
  let val fltAppE_1442_1711 = (sumMass c_194_1308_1703) in 
  let val fltAppE_1443_1712 = (sumMass d_195_1309_1704) in 
  let val fltAppE_1444_1713 = (sumMass e_196_1310_1705) in 
  let val fltAppE_1445_1714 = (sumMass f_197_1311_1706) in 
  let val fltAppE_1446_1715 = (sumMass g_198_1312_1707) in 
  let val fltAppE_1447_1716 = (sumMass h_199_1313_1708) in (sum8(fltAppE_1440_1709 , fltAppE_1441_1710, fltAppE_1442_1711, fltAppE_1443_1712, fltAppE_1444_1713, fltAppE_1445_1714, fltAppE_1446_1715, fltAppE_1447_1716)) end end end end end end end end 
  | Particle (m_200_1314_1717 , wildcard__194_201_1315_1718, wildcard__195_202_1316_1719) => m_200_1314_1717
  | EmptyOct => 0);

fun internal_traverse_Octree (arg_929_1229_1670) = (case arg_929_1229_1670 of Cell (x_930_1230_1671 , x_931_1231_1672, x_932_1232_1673, x_933_1233_1674, x_934_1234_1675, x_935_1235_1676, x_936_1236_1677, x_937_1237_1678, x_938_1238_1679, x_939_1239_1680, x_940_1240_1681, x_941_1241_1682, x_942_1242_1683) => 
  let val y_948_1243_1684 = (internal_traverse_Octree x_935_1235_1676) in 
  let val y_949_1244_1685 = (internal_traverse_Octree x_936_1236_1677) in 
  let val y_950_1245_1686 = (internal_traverse_Octree x_937_1237_1678) in 
  let val y_951_1246_1687 = (internal_traverse_Octree x_938_1238_1679) in 
  let val y_952_1247_1688 = (internal_traverse_Octree x_939_1239_1680) in 
  let val y_953_1248_1689 = (internal_traverse_Octree x_940_1240_1681) in 
  let val y_954_1249_1690 = (internal_traverse_Octree x_941_1241_1682) in 
  let val y_955_1250_1691 = (internal_traverse_Octree x_942_1242_1683) in () end end end end end end end end 
  | Particle (x_956_1251_1692 , x_957_1252_1693, x_958_1253_1694) => ()
  | EmptyOct => ());

fun internal_print_Octree (arg_962_1174_1615) = (case arg_962_1174_1615 of Cell (x_963_1175_1616 , x_964_1176_1617, x_965_1177_1618, x_966_1178_1619, x_967_1179_1620, x_968_1180_1621, x_969_1181_1622, x_970_1182_1623, x_971_1183_1624, x_972_1184_1625, x_973_1185_1626, x_974_1186_1627, x_975_1187_1628) => 
  let val wildcard_989_1188_1629 = (print "(Cell") in 
  let val wildcard_1003_1189_1630 = (print " ") in 
  let val y_976_1190_1631 = (print(Int.toString(x_963_1175_1616))) in 
  let val wildcard_1002_1191_1632 = (print " ") in 
  let val y_977_1192_1633 = (print(Int.toString(x_964_1176_1617))) in 
  let val wildcard_1001_1193_1634 = (print " ") in 
  let val y_978_1194_1635 = (print(Int.toString(x_965_1177_1618))) in 
  let val wildcard_1000_1195_1636 = (print " ") in 
  let val y_979_1196_1637 = (print(Int.toString(x_966_1178_1619))) in 
  let val wildcard_999_1197_1638 = (print " ") in 
  let val y_980_1198_1639 = (print(Int.toString(x_967_1179_1620))) in 
  let val wildcard_998_1199_1640 = (print " ") in 
  let val y_981_1200_1641 = (internal_print_Octree x_968_1180_1621) in 
  let val wildcard_997_1201_1642 = (print " ") in 
  let val y_982_1202_1643 = (internal_print_Octree x_969_1181_1622) in 
  let val wildcard_996_1203_1644 = (print " ") in 
  let val y_983_1204_1645 = (internal_print_Octree x_970_1182_1623) in 
  let val wildcard_995_1205_1646 = (print " ") in 
  let val y_984_1206_1647 = (internal_print_Octree x_971_1183_1624) in 
  let val wildcard_994_1207_1648 = (print " ") in 
  let val y_985_1208_1649 = (internal_print_Octree x_972_1184_1625) in 
  let val wildcard_993_1209_1650 = (print " ") in 
  let val y_986_1210_1651 = (internal_print_Octree x_973_1185_1626) in 
  let val wildcard_992_1211_1652 = (print " ") in 
  let val y_987_1212_1653 = (internal_print_Octree x_974_1186_1627) in 
  let val wildcard_991_1213_1654 = (print " ") in 
  let val y_988_1214_1655 = (internal_print_Octree x_975_1187_1628) in 
  let val wildcard_990_1215_1656 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | Particle (x_1004_1216_1657 , x_1005_1217_1658, x_1006_1218_1659) => 
  let val wildcard_1010_1219_1660 = (print "(Particle") in 
  let val wildcard_1014_1220_1661 = (print " ") in 
  let val y_1007_1221_1662 = (print(Int.toString(x_1004_1216_1657))) in 
  let val wildcard_1013_1222_1663 = (print " ") in 
  let val y_1008_1223_1664 = (print(Int.toString(x_1005_1217_1658))) in 
  let val wildcard_1012_1224_1665 = (print " ") in 
  let val y_1009_1225_1666 = (print(Int.toString(x_1006_1218_1659))) in 
  let val wildcard_1011_1226_1667 = (print ")") in () end end end end end end end end
  | EmptyOct => 
  let val wildcard_1015_1227_1668 = (print "(EmptyOct") in 
  let val wildcard_1016_1228_1669 = (print ")") in () end end);

fun massOf (t_123_1157_1598) = (case t_123_1157_1598 of Cell (m_124_1158_1599 , wildcard__14_125_1159_1600, wildcard__15_126_1160_1601, wildcard__16_127_1161_1602, wildcard__17_128_1162_1603, wildcard__18_129_1163_1604, wildcard__19_130_1164_1605, wildcard__20_131_1165_1606, wildcard__21_132_1166_1607, wildcard__22_133_1167_1608, wildcard__23_134_1168_1609, wildcard__24_135_1169_1610, wildcard__25_136_1170_1611) => m_124_1158_1599 
  | Particle (m_137_1171_1612 , wildcard__39_138_1172_1613, wildcard__40_139_1173_1614) => m_137_1171_1612
  | EmptyOct => 0);

fun weightedPos (t_106_1140_1581) = (case t_106_1140_1581 of Cell (m_107_1141_1582 , c_108_1142_1583, wildcard__45_109_1143_1584, wildcard__46_110_1144_1585, wildcard__47_111_1145_1586, wildcard__48_112_1146_1587, wildcard__49_113_1147_1588, wildcard__50_114_1148_1589, wildcard__51_115_1149_1590, wildcard__52_116_1150_1591, wildcard__53_117_1151_1592, wildcard__54_118_1152_1593, wildcard__55_119_1153_1594) => (m_107_1141_1582 * c_108_1142_1583) 
  | Particle (m_120_1154_1595 , p_121_1155_1596, wildcard__69_122_1156_1597) => (m_120_1154_1595 * p_121_1155_1596)
  | EmptyOct => 0);

fun countOf (t_44_1078_1564) = (case t_44_1078_1564 of Cell (wildcard__74_45_1079_1565 , wildcard__75_46_1080_1566, n_47_1081_1567, wildcard__76_48_1082_1568, wildcard__77_49_1083_1569, wildcard__78_50_1084_1570, wildcard__79_51_1085_1571, wildcard__80_52_1086_1572, wildcard__81_53_1087_1573, wildcard__82_54_1088_1574, wildcard__83_55_1089_1575, wildcard__84_56_1090_1576, wildcard__85_57_1091_1577) => n_47_1081_1567 
  | Particle (wildcard__99_58_1092_1578 , wildcard__100_59_1093_1579, wildcard__101_60_1094_1580) => 1
  | EmptyOct => 0);

fun buildOctree (d_247_1361_1741 , seed_248_1362_1742, center_249_1363_1743, half_250_1364_1744) = 
  let val fltIf_1458_1745 = (d_247_1361_1741 = 0) in 
  (if fltIf_1458_1745 then 
  let val fltPrm_1460_1746 = (absI seed_248_1362_1742) in 
  let val fltPrm_1459_1747 = (fltPrm_1460_1746 mod 5) in 
  let val m_251_1365_1748 = (1 + fltPrm_1459_1747) in 
  let val fltPrm_1463_1749 = (mixSeed(seed_248_1362_1742 , 3)) in 
  let val fltPrm_1462_1750 = (fltPrm_1463_1749 mod 3) in 
  let val fltPrm_1461_1751 = (center_249_1363_1743 + fltPrm_1462_1750) in 
  let val p_252_1366_1752 = (fltPrm_1461_1751 - 1) in 
  let val fltPrm_1465_1753 = (mixSeed(seed_248_1362_1742 , 11)) in 
  let val fltPrm_1464_1754 = (fltPrm_1465_1753 mod 11) in 
  let val v_253_1367_1755 = (fltPrm_1464_1754 - 5) in (Particle (m_251_1365_1748 , p_252_1366_1752, v_253_1367_1755)) end end end end end end end end end end 
   else 
  let val fltAppE_1466_1756 = (half_250_1364_1744 div 2) in 
  let val half__254_1368_1757 = (maxI(1 , fltAppE_1466_1756)) in 
  let val fltAppE_1467_1758 = (half_250_1364_1744 div 4) in 
  let val stride_255_1369_1759 = (maxI(1 , fltAppE_1467_1758)) in 
  let val fltPrm_1468_1760 = (stride_255_1369_1759 * 7) in 
  let val o0_256_1370_1761 = (0 - fltPrm_1468_1760) in 
  let val fltPrm_1469_1762 = (stride_255_1369_1759 * 5) in 
  let val o1_257_1371_1763 = (0 - fltPrm_1469_1762) in 
  let val fltPrm_1470_1764 = (stride_255_1369_1759 * 3) in 
  let val o2_258_1372_1765 = (0 - fltPrm_1470_1764) in 
  let val o3_259_1373_1766 = (0 - stride_255_1369_1759) in 
  let val o5_261_1375_1768 = (stride_255_1369_1759 * 3) in 
  let val o6_262_1376_1769 = (stride_255_1369_1759 * 5) in 
  let val o7_263_1377_1770 = (stride_255_1369_1759 * 7) in 
  let val fltAppE_1471_1771 = (d_247_1361_1741 - 1) in 
  let val fltAppE_1472_1772 = (mixSeed(seed_248_1362_1742 , 1)) in 
  let val fltAppE_1473_1773 = (center_249_1363_1743 + o0_256_1370_1761) in 
  let val c0_264_1378_1774 = (buildOctree(fltAppE_1471_1771 , fltAppE_1472_1772, fltAppE_1473_1773, half__254_1368_1757)) in 
  let val fltAppE_1474_1775 = (d_247_1361_1741 - 1) in 
  let val fltAppE_1475_1776 = (mixSeed(seed_248_1362_1742 , 2)) in 
  let val fltAppE_1476_1777 = (center_249_1363_1743 + o1_257_1371_1763) in 
  let val c1_265_1379_1778 = (buildOctree(fltAppE_1474_1775 , fltAppE_1475_1776, fltAppE_1476_1777, half__254_1368_1757)) in 
  let val fltAppE_1477_1779 = (d_247_1361_1741 - 1) in 
  let val fltAppE_1478_1780 = (mixSeed(seed_248_1362_1742 , 3)) in 
  let val fltAppE_1479_1781 = (center_249_1363_1743 + o2_258_1372_1765) in 
  let val c2_266_1380_1782 = (buildOctree(fltAppE_1477_1779 , fltAppE_1478_1780, fltAppE_1479_1781, half__254_1368_1757)) in 
  let val fltAppE_1480_1783 = (d_247_1361_1741 - 1) in 
  let val fltAppE_1481_1784 = (mixSeed(seed_248_1362_1742 , 4)) in 
  let val fltAppE_1482_1785 = (center_249_1363_1743 + o3_259_1373_1766) in 
  let val c3_267_1381_1786 = (buildOctree(fltAppE_1480_1783 , fltAppE_1481_1784, fltAppE_1482_1785, half__254_1368_1757)) in 
  let val fltAppE_1483_1787 = (d_247_1361_1741 - 1) in 
  let val fltAppE_1484_1788 = (mixSeed(seed_248_1362_1742 , 5)) in 
  let val fltAppE_1485_1789 = (center_249_1363_1743 + stride_255_1369_1759) in 
  let val c4_268_1382_1790 = (buildOctree(fltAppE_1483_1787 , fltAppE_1484_1788, fltAppE_1485_1789, half__254_1368_1757)) in 
  let val fltAppE_1486_1791 = (d_247_1361_1741 - 1) in 
  let val fltAppE_1487_1792 = (mixSeed(seed_248_1362_1742 , 6)) in 
  let val fltAppE_1488_1793 = (center_249_1363_1743 + o5_261_1375_1768) in 
  let val c5_269_1383_1794 = (buildOctree(fltAppE_1486_1791 , fltAppE_1487_1792, fltAppE_1488_1793, half__254_1368_1757)) in 
  let val fltAppE_1489_1795 = (d_247_1361_1741 - 1) in 
  let val fltAppE_1490_1796 = (mixSeed(seed_248_1362_1742 , 7)) in 
  let val fltAppE_1491_1797 = (center_249_1363_1743 + o6_262_1376_1769) in 
  let val c6_270_1384_1798 = (buildOctree(fltAppE_1489_1795 , fltAppE_1490_1796, fltAppE_1491_1797, half__254_1368_1757)) in 
  let val fltAppE_1492_1799 = (d_247_1361_1741 - 1) in 
  let val fltAppE_1493_1800 = (mixSeed(seed_248_1362_1742 , 8)) in 
  let val fltAppE_1494_1801 = (center_249_1363_1743 + o7_263_1377_1770) in 
  let val c7_271_1385_1802 = (buildOctree(fltAppE_1492_1799 , fltAppE_1493_1800, fltAppE_1494_1801, half__254_1368_1757)) in 
  let val m0_272_1386_1803 = (massOf c0_264_1378_1774) in 
  let val m1_273_1387_1804 = (massOf c1_265_1379_1778) in 
  let val m2_274_1388_1805 = (massOf c2_266_1380_1782) in 
  let val m3_275_1389_1806 = (massOf c3_267_1381_1786) in 
  let val m4_276_1390_1807 = (massOf c4_268_1382_1790) in 
  let val m5_277_1391_1808 = (massOf c5_269_1383_1794) in 
  let val m6_278_1392_1809 = (massOf c6_270_1384_1798) in 
  let val m7_279_1393_1810 = (massOf c7_271_1385_1802) in 
  let val mTot_280_1394_1811 = (sum8(m0_272_1386_1803 , m1_273_1387_1804, m2_274_1388_1805, m3_275_1389_1806, m4_276_1390_1807, m5_277_1391_1808, m6_278_1392_1809, m7_279_1393_1810)) in 
  let val fltAppE_1495_1812 = (weightedPos c0_264_1378_1774) in 
  let val fltAppE_1496_1813 = (weightedPos c1_265_1379_1778) in 
  let val fltAppE_1497_1814 = (weightedPos c2_266_1380_1782) in 
  let val fltAppE_1498_1815 = (weightedPos c3_267_1381_1786) in 
  let val fltAppE_1499_1816 = (weightedPos c4_268_1382_1790) in 
  let val fltAppE_1500_1817 = (weightedPos c5_269_1383_1794) in 
  let val fltAppE_1501_1818 = (weightedPos c6_270_1384_1798) in 
  let val fltAppE_1502_1819 = (weightedPos c7_271_1385_1802) in 
  let val wTot_281_1395_1820 = (sum8(fltAppE_1495_1812 , fltAppE_1496_1813, fltAppE_1497_1814, fltAppE_1498_1815, fltAppE_1499_1816, fltAppE_1500_1817, fltAppE_1501_1818, fltAppE_1502_1819)) in 
  let val fltAppE_1503_1821 = (countOf c0_264_1378_1774) in 
  let val fltAppE_1504_1822 = (countOf c1_265_1379_1778) in 
  let val fltAppE_1505_1823 = (countOf c2_266_1380_1782) in 
  let val fltAppE_1506_1824 = (countOf c3_267_1381_1786) in 
  let val fltAppE_1507_1825 = (countOf c4_268_1382_1790) in 
  let val fltAppE_1508_1826 = (countOf c5_269_1383_1794) in 
  let val fltAppE_1509_1827 = (countOf c6_270_1384_1798) in 
  let val fltAppE_1510_1828 = (countOf c7_271_1385_1802) in 
  let val nTot_282_1396_1829 = (sum8(fltAppE_1503_1821 , fltAppE_1504_1822, fltAppE_1505_1823, fltAppE_1506_1824, fltAppE_1507_1825, fltAppE_1508_1826, fltAppE_1509_1827, fltAppE_1510_1828)) in 
  let val fltAppE_1511_1830 = (momentumOf c0_264_1378_1774) in 
  let val fltAppE_1512_1831 = (momentumOf c1_265_1379_1778) in 
  let val fltAppE_1513_1832 = (momentumOf c2_266_1380_1782) in 
  let val fltAppE_1514_1833 = (momentumOf c3_267_1381_1786) in 
  let val fltAppE_1515_1834 = (momentumOf c4_268_1382_1790) in 
  let val fltAppE_1516_1835 = (momentumOf c5_269_1383_1794) in 
  let val fltAppE_1517_1836 = (momentumOf c6_270_1384_1798) in 
  let val fltAppE_1518_1837 = (momentumOf c7_271_1385_1802) in 
  let val pTot_283_1397_1838 = (sum8(fltAppE_1511_1830 , fltAppE_1512_1831, fltAppE_1513_1832, fltAppE_1514_1833, fltAppE_1515_1834, fltAppE_1516_1835, fltAppE_1517_1836, fltAppE_1518_1837)) in 
  let val fltIf_1519_1839 = (mTot_280_1394_1811 = 0) in 
  let val com_284_1398_1840 = 
  (if fltIf_1519_1839 then center_249_1363_1743 
   else (wTot_281_1395_1820 div mTot_280_1394_1811)) in (Cell (mTot_280_1394_1811 , com_284_1398_1840, nTot_282_1396_1829, half_250_1364_1744, pTot_283_1397_1838, c0_264_1378_1774, c1_265_1379_1778, c2_266_1380_1782, c3_267_1381_1786, c4_268_1382_1790, c5_269_1383_1794, c6_270_1384_1798, c7_271_1385_1802)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end) end;

fun internal_copy_Octree (arg_896_1025_1531) = (case arg_896_1025_1531 of Cell (x_897_1026_1532 , x_898_1027_1533, x_899_1028_1534, x_900_1029_1535, x_901_1030_1536, x_902_1031_1537, x_903_1032_1538, x_904_1033_1539, x_905_1034_1540, x_906_1035_1541, x_907_1036_1542, x_908_1037_1543, x_909_1038_1544) => 
  let val y_915_1044_1550 = (internal_copy_Octree x_902_1031_1537) in 
  let val y_916_1045_1551 = (internal_copy_Octree x_903_1032_1538) in 
  let val y_917_1046_1552 = (internal_copy_Octree x_904_1033_1539) in 
  let val y_918_1047_1553 = (internal_copy_Octree x_905_1034_1540) in 
  let val y_919_1048_1554 = (internal_copy_Octree x_906_1035_1541) in 
  let val y_920_1049_1555 = (internal_copy_Octree x_907_1036_1542) in 
  let val y_921_1050_1556 = (internal_copy_Octree x_908_1037_1543) in 
  let val y_922_1051_1557 = (internal_copy_Octree x_909_1038_1544) in (Cell (x_897_1026_1532 , x_898_1027_1533, x_899_1028_1534, x_900_1029_1535, x_901_1030_1536, y_915_1044_1550, y_916_1045_1551, y_917_1046_1552, y_918_1047_1553, y_919_1048_1554, y_920_1049_1555, y_921_1050_1556, y_922_1051_1557)) end end end end end end end end 
  | Particle (x_923_1052_1558 , x_924_1053_1559, x_925_1054_1560) => (Particle (x_923_1052_1558 , x_924_1053_1559, x_925_1054_1560))
  | EmptyOct => EmptyOct);
val _ = (print(Int.toString(
  let val wildcard__13_16_1017_1521 = (print "Running program OctTree Physics Simulation: ") in 
  let val wildcard__11_17_1018_1522 = (print "NEWLINE") in 
  let val fltPrm_1439_1523 = 1 in 
  let val fltAppE_1438_1524 = (fltPrm_1439_1523 + 8) in 
  let val octTree_18_1019_1525 = (buildOctree(fltAppE_1438_1524 , 17, 0, 64)) in 
  let val wildcard__8_19_1020_1526 = (print "Running pass sumMass (fold, uses=10): ") in 
  let val wildcard__6_20_1021_1527 = (print "NEWLINE") in 
  let val totMass_21_1022_1528 = (sumMass octTree_18_1019_1525) in 
  let val wildcard__2_22_1023_1529 = (print "End") in 
  let val wildcard__0_23_1024_1530 = (print "NEWLINE") in totMass_21_1022_1528 end end end end end end end end end end)));
val _ = print "\n"
