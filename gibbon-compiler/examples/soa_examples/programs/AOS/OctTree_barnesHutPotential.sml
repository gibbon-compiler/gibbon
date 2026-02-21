datatype dat_Octree = Cell of (int  * int * int * int * int *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree) | Particle of (int  * int * int)| EmptyOct ;

fun maxI (a_302_1416_1886 , b_303_1417_1887) = 
  let val fltIf_1530_1888 = (a_302_1416_1886 > b_303_1417_1887) in 
  (if fltIf_1530_1888 then a_302_1416_1886 
   else b_303_1417_1887) end;

fun momentumOf (t_285_1399_1869) = (case t_285_1399_1869 of Cell (wildcard__106_286_1400_1870 , wildcard__107_287_1401_1871, wildcard__108_288_1402_1872, wildcard__109_289_1403_1873, mom_290_1404_1874, wildcard__110_291_1405_1875, wildcard__111_292_1406_1876, wildcard__112_293_1407_1877, wildcard__113_294_1408_1878, wildcard__114_295_1409_1879, wildcard__115_296_1410_1880, wildcard__116_297_1411_1881, wildcard__117_298_1412_1882) => mom_290_1404_1874 
  | Particle (m_299_1413_1883 , wildcard__131_300_1414_1884, v_301_1415_1885) => (m_299_1413_1883 * v_301_1415_1885)
  | EmptyOct => 0);

fun sum8 (a_239_1353_1755 , b_240_1354_1756, c_241_1355_1757, d_242_1356_1758, e_243_1357_1759, f_244_1358_1760, g_245_1359_1761, h_246_1360_1762) = 
  let val fltPrm_1467_1763 = (a_239_1353_1755 + b_240_1354_1756) in 
  let val fltPrm_1466_1764 = (fltPrm_1467_1763 + c_241_1355_1757) in 
  let val fltPrm_1465_1765 = (fltPrm_1466_1764 + d_242_1356_1758) in 
  let val fltPrm_1464_1766 = (fltPrm_1465_1765 + e_243_1357_1759) in 
  let val fltPrm_1463_1767 = (fltPrm_1464_1766 + f_244_1358_1760) in 
  let val fltPrm_1462_1768 = (fltPrm_1463_1767 + g_245_1359_1761) in (fltPrm_1462_1768 + h_246_1360_1762) end end end end end end;

fun absI (x_238_1352_1753) = 
  let val fltIf_1461_1754 = (x_238_1352_1753 < 0) in 
  (if fltIf_1461_1754 then (0 - x_238_1352_1753) 
   else x_238_1352_1753) end;

fun mixSeed (s_228_1342_1748 , salt_229_1343_1749) = 
  let val fltPrm_1459_1750 = (s_228_1342_1748 * 1103) in 
  let val fltPrm_1460_1751 = (salt_229_1343_1749 * 97) in 
  let val fltPrm_1458_1752 = (fltPrm_1459_1750 + fltPrm_1460_1751) in (fltPrm_1458_1752 + 13) end end end;

fun barnesHutPotential (t_203_1317_1705 , probe_204_1318_1706, theta_205_1319_1707) = (case t_203_1317_1705 of Cell (m_206_1320_1708 , c_207_1321_1709, n_208_1322_1710, s_209_1323_1711, wildcard__278_210_1324_1712, a_211_1325_1713, b_212_1326_1714, c1_213_1327_1715, d_214_1328_1716, e_215_1329_1717, f_216_1330_1718, g_217_1331_1719, h_218_1332_1720) => 
  let val fltAppE_1441_1721 = (c_207_1321_1709 - probe_204_1318_1706) in 
  let val fltPrm_1440_1722 = (absI fltAppE_1441_1721) in 
  let val dist_219_1333_1723 = (fltPrm_1440_1722 + 1) in 
  let val openLhs_220_1334_1724 = (s_209_1323_1711 * 100) in 
  let val openRhs_221_1335_1725 = (theta_205_1319_1707 * dist_219_1333_1723) in 
  let val fltIf_1442_1726 = (n_208_1322_1710 = 0) in 
  let val approx_222_1336_1729 = 
  (if fltIf_1442_1726 then 0 
   else 
  let val fltPrm_1443_1727 = (m_206_1320_1708 * 1000) in 
  let val fltPrm_1444_1728 = (dist_219_1333_1723 * dist_219_1333_1723) in (fltPrm_1443_1727 div fltPrm_1444_1728) end end) in 
  let val fltAppE_1445_1730 = (barnesHutPotential(a_211_1325_1713 , probe_204_1318_1706, theta_205_1319_1707)) in 
  let val fltAppE_1446_1731 = (barnesHutPotential(b_212_1326_1714 , probe_204_1318_1706, theta_205_1319_1707)) in 
  let val fltAppE_1447_1732 = (barnesHutPotential(c1_213_1327_1715 , probe_204_1318_1706, theta_205_1319_1707)) in 
  let val fltAppE_1448_1733 = (barnesHutPotential(d_214_1328_1716 , probe_204_1318_1706, theta_205_1319_1707)) in 
  let val fltAppE_1449_1734 = (barnesHutPotential(e_215_1329_1717 , probe_204_1318_1706, theta_205_1319_1707)) in 
  let val fltAppE_1450_1735 = (barnesHutPotential(f_216_1330_1718 , probe_204_1318_1706, theta_205_1319_1707)) in 
  let val fltAppE_1451_1736 = (barnesHutPotential(g_217_1331_1719 , probe_204_1318_1706, theta_205_1319_1707)) in 
  let val fltAppE_1452_1737 = (barnesHutPotential(h_218_1332_1720 , probe_204_1318_1706, theta_205_1319_1707)) in 
  let val recur_223_1337_1738 = (sum8(fltAppE_1445_1730 , fltAppE_1446_1731, fltAppE_1447_1732, fltAppE_1448_1733, fltAppE_1449_1734, fltAppE_1450_1735, fltAppE_1451_1736, fltAppE_1452_1737)) in 
  let val fltIf_1453_1739 = (openLhs_220_1334_1724 < openRhs_221_1335_1725) in 
  (if fltIf_1453_1739 then approx_222_1336_1729 
   else recur_223_1337_1738) end end end end end end end end end end end end end end end end end 
  | Particle (m_224_1338_1740 , p_225_1339_1741, wildcard__297_226_1340_1742) => 
  let val fltAppE_1455_1743 = (p_225_1339_1741 - probe_204_1318_1706) in 
  let val fltPrm_1454_1744 = (absI fltAppE_1455_1743) in 
  let val dist_227_1341_1745 = (fltPrm_1454_1744 + 1) in 
  let val fltPrm_1456_1746 = (m_224_1338_1740 * 1000) in 
  let val fltPrm_1457_1747 = (dist_227_1341_1745 * dist_227_1341_1745) in (fltPrm_1456_1746 div fltPrm_1457_1747) end end end end end
  | EmptyOct => 0);

fun internal_traverse_Octree (arg_929_1229_1680) = (case arg_929_1229_1680 of Cell (x_930_1230_1681 , x_931_1231_1682, x_932_1232_1683, x_933_1233_1684, x_934_1234_1685, x_935_1235_1686, x_936_1236_1687, x_937_1237_1688, x_938_1238_1689, x_939_1239_1690, x_940_1240_1691, x_941_1241_1692, x_942_1242_1693) => 
  let val y_948_1243_1694 = (internal_traverse_Octree x_935_1235_1686) in 
  let val y_949_1244_1695 = (internal_traverse_Octree x_936_1236_1687) in 
  let val y_950_1245_1696 = (internal_traverse_Octree x_937_1237_1688) in 
  let val y_951_1246_1697 = (internal_traverse_Octree x_938_1238_1689) in 
  let val y_952_1247_1698 = (internal_traverse_Octree x_939_1239_1690) in 
  let val y_953_1248_1699 = (internal_traverse_Octree x_940_1240_1691) in 
  let val y_954_1249_1700 = (internal_traverse_Octree x_941_1241_1692) in 
  let val y_955_1250_1701 = (internal_traverse_Octree x_942_1242_1693) in () end end end end end end end end 
  | Particle (x_956_1251_1702 , x_957_1252_1703, x_958_1253_1704) => ()
  | EmptyOct => ());

fun internal_print_Octree (arg_962_1174_1625) = (case arg_962_1174_1625 of Cell (x_963_1175_1626 , x_964_1176_1627, x_965_1177_1628, x_966_1178_1629, x_967_1179_1630, x_968_1180_1631, x_969_1181_1632, x_970_1182_1633, x_971_1183_1634, x_972_1184_1635, x_973_1185_1636, x_974_1186_1637, x_975_1187_1638) => 
  let val wildcard_989_1188_1639 = (print "(Cell") in 
  let val wildcard_1003_1189_1640 = (print " ") in 
  let val y_976_1190_1641 = (print(Int.toString(x_963_1175_1626))) in 
  let val wildcard_1002_1191_1642 = (print " ") in 
  let val y_977_1192_1643 = (print(Int.toString(x_964_1176_1627))) in 
  let val wildcard_1001_1193_1644 = (print " ") in 
  let val y_978_1194_1645 = (print(Int.toString(x_965_1177_1628))) in 
  let val wildcard_1000_1195_1646 = (print " ") in 
  let val y_979_1196_1647 = (print(Int.toString(x_966_1178_1629))) in 
  let val wildcard_999_1197_1648 = (print " ") in 
  let val y_980_1198_1649 = (print(Int.toString(x_967_1179_1630))) in 
  let val wildcard_998_1199_1650 = (print " ") in 
  let val y_981_1200_1651 = (internal_print_Octree x_968_1180_1631) in 
  let val wildcard_997_1201_1652 = (print " ") in 
  let val y_982_1202_1653 = (internal_print_Octree x_969_1181_1632) in 
  let val wildcard_996_1203_1654 = (print " ") in 
  let val y_983_1204_1655 = (internal_print_Octree x_970_1182_1633) in 
  let val wildcard_995_1205_1656 = (print " ") in 
  let val y_984_1206_1657 = (internal_print_Octree x_971_1183_1634) in 
  let val wildcard_994_1207_1658 = (print " ") in 
  let val y_985_1208_1659 = (internal_print_Octree x_972_1184_1635) in 
  let val wildcard_993_1209_1660 = (print " ") in 
  let val y_986_1210_1661 = (internal_print_Octree x_973_1185_1636) in 
  let val wildcard_992_1211_1662 = (print " ") in 
  let val y_987_1212_1663 = (internal_print_Octree x_974_1186_1637) in 
  let val wildcard_991_1213_1664 = (print " ") in 
  let val y_988_1214_1665 = (internal_print_Octree x_975_1187_1638) in 
  let val wildcard_990_1215_1666 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | Particle (x_1004_1216_1667 , x_1005_1217_1668, x_1006_1218_1669) => 
  let val wildcard_1010_1219_1670 = (print "(Particle") in 
  let val wildcard_1014_1220_1671 = (print " ") in 
  let val y_1007_1221_1672 = (print(Int.toString(x_1004_1216_1667))) in 
  let val wildcard_1013_1222_1673 = (print " ") in 
  let val y_1008_1223_1674 = (print(Int.toString(x_1005_1217_1668))) in 
  let val wildcard_1012_1224_1675 = (print " ") in 
  let val y_1009_1225_1676 = (print(Int.toString(x_1006_1218_1669))) in 
  let val wildcard_1011_1226_1677 = (print ")") in () end end end end end end end end
  | EmptyOct => 
  let val wildcard_1015_1227_1678 = (print "(EmptyOct") in 
  let val wildcard_1016_1228_1679 = (print ")") in () end end);

fun massOf (t_123_1157_1608) = (case t_123_1157_1608 of Cell (m_124_1158_1609 , wildcard__14_125_1159_1610, wildcard__15_126_1160_1611, wildcard__16_127_1161_1612, wildcard__17_128_1162_1613, wildcard__18_129_1163_1614, wildcard__19_130_1164_1615, wildcard__20_131_1165_1616, wildcard__21_132_1166_1617, wildcard__22_133_1167_1618, wildcard__23_134_1168_1619, wildcard__24_135_1169_1620, wildcard__25_136_1170_1621) => m_124_1158_1609 
  | Particle (m_137_1171_1622 , wildcard__39_138_1172_1623, wildcard__40_139_1173_1624) => m_137_1171_1622
  | EmptyOct => 0);

fun weightedPos (t_106_1140_1591) = (case t_106_1140_1591 of Cell (m_107_1141_1592 , c_108_1142_1593, wildcard__45_109_1143_1594, wildcard__46_110_1144_1595, wildcard__47_111_1145_1596, wildcard__48_112_1146_1597, wildcard__49_113_1147_1598, wildcard__50_114_1148_1599, wildcard__51_115_1149_1600, wildcard__52_116_1150_1601, wildcard__53_117_1151_1602, wildcard__54_118_1152_1603, wildcard__55_119_1153_1604) => (m_107_1141_1592 * c_108_1142_1593) 
  | Particle (m_120_1154_1605 , p_121_1155_1606, wildcard__69_122_1156_1607) => (m_120_1154_1605 * p_121_1155_1606)
  | EmptyOct => 0);

fun countOf (t_44_1078_1574) = (case t_44_1078_1574 of Cell (wildcard__74_45_1079_1575 , wildcard__75_46_1080_1576, n_47_1081_1577, wildcard__76_48_1082_1578, wildcard__77_49_1083_1579, wildcard__78_50_1084_1580, wildcard__79_51_1085_1581, wildcard__80_52_1086_1582, wildcard__81_53_1087_1583, wildcard__82_54_1088_1584, wildcard__83_55_1089_1585, wildcard__84_56_1090_1586, wildcard__85_57_1091_1587) => n_47_1081_1577 
  | Particle (wildcard__99_58_1092_1588 , wildcard__100_59_1093_1589, wildcard__101_60_1094_1590) => 1
  | EmptyOct => 0);

fun buildOctree (d_247_1361_1769 , seed_248_1362_1770, center_249_1363_1771, half_250_1364_1772) = 
  let val fltIf_1468_1773 = (d_247_1361_1769 = 0) in 
  (if fltIf_1468_1773 then 
  let val fltPrm_1470_1774 = (absI seed_248_1362_1770) in 
  let val fltPrm_1469_1775 = (fltPrm_1470_1774 mod 5) in 
  let val m_251_1365_1776 = (1 + fltPrm_1469_1775) in 
  let val fltPrm_1473_1777 = (mixSeed(seed_248_1362_1770 , 3)) in 
  let val fltPrm_1472_1778 = (fltPrm_1473_1777 mod 3) in 
  let val fltPrm_1471_1779 = (center_249_1363_1771 + fltPrm_1472_1778) in 
  let val p_252_1366_1780 = (fltPrm_1471_1779 - 1) in 
  let val fltPrm_1475_1781 = (mixSeed(seed_248_1362_1770 , 11)) in 
  let val fltPrm_1474_1782 = (fltPrm_1475_1781 mod 11) in 
  let val v_253_1367_1783 = (fltPrm_1474_1782 - 5) in (Particle (m_251_1365_1776 , p_252_1366_1780, v_253_1367_1783)) end end end end end end end end end end 
   else 
  let val fltAppE_1476_1784 = (half_250_1364_1772 div 2) in 
  let val half__254_1368_1785 = (maxI(1 , fltAppE_1476_1784)) in 
  let val fltAppE_1477_1786 = (half_250_1364_1772 div 4) in 
  let val stride_255_1369_1787 = (maxI(1 , fltAppE_1477_1786)) in 
  let val fltPrm_1478_1788 = (stride_255_1369_1787 * 7) in 
  let val o0_256_1370_1789 = (0 - fltPrm_1478_1788) in 
  let val fltPrm_1479_1790 = (stride_255_1369_1787 * 5) in 
  let val o1_257_1371_1791 = (0 - fltPrm_1479_1790) in 
  let val fltPrm_1480_1792 = (stride_255_1369_1787 * 3) in 
  let val o2_258_1372_1793 = (0 - fltPrm_1480_1792) in 
  let val o3_259_1373_1794 = (0 - stride_255_1369_1787) in 
  let val o5_261_1375_1796 = (stride_255_1369_1787 * 3) in 
  let val o6_262_1376_1797 = (stride_255_1369_1787 * 5) in 
  let val o7_263_1377_1798 = (stride_255_1369_1787 * 7) in 
  let val fltAppE_1481_1799 = (d_247_1361_1769 - 1) in 
  let val fltAppE_1482_1800 = (mixSeed(seed_248_1362_1770 , 1)) in 
  let val fltAppE_1483_1801 = (center_249_1363_1771 + o0_256_1370_1789) in 
  let val c0_264_1378_1802 = (buildOctree(fltAppE_1481_1799 , fltAppE_1482_1800, fltAppE_1483_1801, half__254_1368_1785)) in 
  let val fltAppE_1484_1803 = (d_247_1361_1769 - 1) in 
  let val fltAppE_1485_1804 = (mixSeed(seed_248_1362_1770 , 2)) in 
  let val fltAppE_1486_1805 = (center_249_1363_1771 + o1_257_1371_1791) in 
  let val c1_265_1379_1806 = (buildOctree(fltAppE_1484_1803 , fltAppE_1485_1804, fltAppE_1486_1805, half__254_1368_1785)) in 
  let val fltAppE_1487_1807 = (d_247_1361_1769 - 1) in 
  let val fltAppE_1488_1808 = (mixSeed(seed_248_1362_1770 , 3)) in 
  let val fltAppE_1489_1809 = (center_249_1363_1771 + o2_258_1372_1793) in 
  let val c2_266_1380_1810 = (buildOctree(fltAppE_1487_1807 , fltAppE_1488_1808, fltAppE_1489_1809, half__254_1368_1785)) in 
  let val fltAppE_1490_1811 = (d_247_1361_1769 - 1) in 
  let val fltAppE_1491_1812 = (mixSeed(seed_248_1362_1770 , 4)) in 
  let val fltAppE_1492_1813 = (center_249_1363_1771 + o3_259_1373_1794) in 
  let val c3_267_1381_1814 = (buildOctree(fltAppE_1490_1811 , fltAppE_1491_1812, fltAppE_1492_1813, half__254_1368_1785)) in 
  let val fltAppE_1493_1815 = (d_247_1361_1769 - 1) in 
  let val fltAppE_1494_1816 = (mixSeed(seed_248_1362_1770 , 5)) in 
  let val fltAppE_1495_1817 = (center_249_1363_1771 + stride_255_1369_1787) in 
  let val c4_268_1382_1818 = (buildOctree(fltAppE_1493_1815 , fltAppE_1494_1816, fltAppE_1495_1817, half__254_1368_1785)) in 
  let val fltAppE_1496_1819 = (d_247_1361_1769 - 1) in 
  let val fltAppE_1497_1820 = (mixSeed(seed_248_1362_1770 , 6)) in 
  let val fltAppE_1498_1821 = (center_249_1363_1771 + o5_261_1375_1796) in 
  let val c5_269_1383_1822 = (buildOctree(fltAppE_1496_1819 , fltAppE_1497_1820, fltAppE_1498_1821, half__254_1368_1785)) in 
  let val fltAppE_1499_1823 = (d_247_1361_1769 - 1) in 
  let val fltAppE_1500_1824 = (mixSeed(seed_248_1362_1770 , 7)) in 
  let val fltAppE_1501_1825 = (center_249_1363_1771 + o6_262_1376_1797) in 
  let val c6_270_1384_1826 = (buildOctree(fltAppE_1499_1823 , fltAppE_1500_1824, fltAppE_1501_1825, half__254_1368_1785)) in 
  let val fltAppE_1502_1827 = (d_247_1361_1769 - 1) in 
  let val fltAppE_1503_1828 = (mixSeed(seed_248_1362_1770 , 8)) in 
  let val fltAppE_1504_1829 = (center_249_1363_1771 + o7_263_1377_1798) in 
  let val c7_271_1385_1830 = (buildOctree(fltAppE_1502_1827 , fltAppE_1503_1828, fltAppE_1504_1829, half__254_1368_1785)) in 
  let val m0_272_1386_1831 = (massOf c0_264_1378_1802) in 
  let val m1_273_1387_1832 = (massOf c1_265_1379_1806) in 
  let val m2_274_1388_1833 = (massOf c2_266_1380_1810) in 
  let val m3_275_1389_1834 = (massOf c3_267_1381_1814) in 
  let val m4_276_1390_1835 = (massOf c4_268_1382_1818) in 
  let val m5_277_1391_1836 = (massOf c5_269_1383_1822) in 
  let val m6_278_1392_1837 = (massOf c6_270_1384_1826) in 
  let val m7_279_1393_1838 = (massOf c7_271_1385_1830) in 
  let val mTot_280_1394_1839 = (sum8(m0_272_1386_1831 , m1_273_1387_1832, m2_274_1388_1833, m3_275_1389_1834, m4_276_1390_1835, m5_277_1391_1836, m6_278_1392_1837, m7_279_1393_1838)) in 
  let val fltAppE_1505_1840 = (weightedPos c0_264_1378_1802) in 
  let val fltAppE_1506_1841 = (weightedPos c1_265_1379_1806) in 
  let val fltAppE_1507_1842 = (weightedPos c2_266_1380_1810) in 
  let val fltAppE_1508_1843 = (weightedPos c3_267_1381_1814) in 
  let val fltAppE_1509_1844 = (weightedPos c4_268_1382_1818) in 
  let val fltAppE_1510_1845 = (weightedPos c5_269_1383_1822) in 
  let val fltAppE_1511_1846 = (weightedPos c6_270_1384_1826) in 
  let val fltAppE_1512_1847 = (weightedPos c7_271_1385_1830) in 
  let val wTot_281_1395_1848 = (sum8(fltAppE_1505_1840 , fltAppE_1506_1841, fltAppE_1507_1842, fltAppE_1508_1843, fltAppE_1509_1844, fltAppE_1510_1845, fltAppE_1511_1846, fltAppE_1512_1847)) in 
  let val fltAppE_1513_1849 = (countOf c0_264_1378_1802) in 
  let val fltAppE_1514_1850 = (countOf c1_265_1379_1806) in 
  let val fltAppE_1515_1851 = (countOf c2_266_1380_1810) in 
  let val fltAppE_1516_1852 = (countOf c3_267_1381_1814) in 
  let val fltAppE_1517_1853 = (countOf c4_268_1382_1818) in 
  let val fltAppE_1518_1854 = (countOf c5_269_1383_1822) in 
  let val fltAppE_1519_1855 = (countOf c6_270_1384_1826) in 
  let val fltAppE_1520_1856 = (countOf c7_271_1385_1830) in 
  let val nTot_282_1396_1857 = (sum8(fltAppE_1513_1849 , fltAppE_1514_1850, fltAppE_1515_1851, fltAppE_1516_1852, fltAppE_1517_1853, fltAppE_1518_1854, fltAppE_1519_1855, fltAppE_1520_1856)) in 
  let val fltAppE_1521_1858 = (momentumOf c0_264_1378_1802) in 
  let val fltAppE_1522_1859 = (momentumOf c1_265_1379_1806) in 
  let val fltAppE_1523_1860 = (momentumOf c2_266_1380_1810) in 
  let val fltAppE_1524_1861 = (momentumOf c3_267_1381_1814) in 
  let val fltAppE_1525_1862 = (momentumOf c4_268_1382_1818) in 
  let val fltAppE_1526_1863 = (momentumOf c5_269_1383_1822) in 
  let val fltAppE_1527_1864 = (momentumOf c6_270_1384_1826) in 
  let val fltAppE_1528_1865 = (momentumOf c7_271_1385_1830) in 
  let val pTot_283_1397_1866 = (sum8(fltAppE_1521_1858 , fltAppE_1522_1859, fltAppE_1523_1860, fltAppE_1524_1861, fltAppE_1525_1862, fltAppE_1526_1863, fltAppE_1527_1864, fltAppE_1528_1865)) in 
  let val fltIf_1529_1867 = (mTot_280_1394_1839 = 0) in 
  let val com_284_1398_1868 = 
  (if fltIf_1529_1867 then center_249_1363_1771 
   else (wTot_281_1395_1848 div mTot_280_1394_1839)) in (Cell (mTot_280_1394_1839 , com_284_1398_1868, nTot_282_1396_1857, half_250_1364_1772, pTot_283_1397_1866, c0_264_1378_1802, c1_265_1379_1806, c2_266_1380_1810, c3_267_1381_1814, c4_268_1382_1818, c5_269_1383_1822, c6_270_1384_1826, c7_271_1385_1830)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end) end;

fun internal_copy_Octree (arg_896_1025_1541) = (case arg_896_1025_1541 of Cell (x_897_1026_1542 , x_898_1027_1543, x_899_1028_1544, x_900_1029_1545, x_901_1030_1546, x_902_1031_1547, x_903_1032_1548, x_904_1033_1549, x_905_1034_1550, x_906_1035_1551, x_907_1036_1552, x_908_1037_1553, x_909_1038_1554) => 
  let val y_915_1044_1560 = (internal_copy_Octree x_902_1031_1547) in 
  let val y_916_1045_1561 = (internal_copy_Octree x_903_1032_1548) in 
  let val y_917_1046_1562 = (internal_copy_Octree x_904_1033_1549) in 
  let val y_918_1047_1563 = (internal_copy_Octree x_905_1034_1550) in 
  let val y_919_1048_1564 = (internal_copy_Octree x_906_1035_1551) in 
  let val y_920_1049_1565 = (internal_copy_Octree x_907_1036_1552) in 
  let val y_921_1050_1566 = (internal_copy_Octree x_908_1037_1553) in 
  let val y_922_1051_1567 = (internal_copy_Octree x_909_1038_1554) in (Cell (x_897_1026_1542 , x_898_1027_1543, x_899_1028_1544, x_900_1029_1545, x_901_1030_1546, y_915_1044_1560, y_916_1045_1561, y_917_1046_1562, y_918_1047_1563, y_919_1048_1564, y_920_1049_1565, y_921_1050_1566, y_922_1051_1567)) end end end end end end end end 
  | Particle (x_923_1052_1568 , x_924_1053_1569, x_925_1054_1570) => (Particle (x_923_1052_1568 , x_924_1053_1569, x_925_1054_1570))
  | EmptyOct => EmptyOct);
val _ = (print(Int.toString(
  let val wildcard__13_16_1017_1531 = (print "Running program OctTree Physics Simulation: ") in 
  let val wildcard__11_17_1018_1532 = (print "NEWLINE") in 
  let val fltPrm_1439_1533 = 1 in 
  let val fltAppE_1438_1534 = (fltPrm_1439_1533 + 8) in 
  let val octTree_18_1019_1535 = (buildOctree(fltAppE_1438_1534 , 17, 0, 64)) in 
  let val wildcard__8_19_1020_1536 = (print "Running pass barnesHutPotential (fold_like, uses=11): ") in 
  let val wildcard__6_20_1021_1537 = (print "NEWLINE") in 
  let val bhPotential_21_1022_1538 = (barnesHutPotential(octTree_18_1019_1535 , 21, 60)) in 
  let val wildcard__2_22_1023_1539 = (print "End") in 
  let val wildcard__0_23_1024_1540 = (print "NEWLINE") in bhPotential_21_1022_1538 end end end end end end end end end end)));
val _ = print "\n"
