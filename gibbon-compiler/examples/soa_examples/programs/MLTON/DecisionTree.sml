open GibbonCompat;

datatype dat_DTree = Leaf of (int  * int) | Node of (int  * int * int *  dat_DTree *  dat_DTree) ;

fun internal_copy_DTree (arg_1209_1531_1919) = (case arg_1209_1531_1919 of Leaf (x_1210_1532_1920 , x_1211_1533_1921) => (Leaf (x_1210_1532_1920 , x_1211_1533_1921)) 
  | Node (x_1214_1536_1924 , x_1215_1537_1925, x_1216_1538_1926, x_1217_1539_1927, x_1218_1540_1928) => 
  let val y_1222_1544_1932 = (internal_copy_DTree x_1217_1539_1927) in 
  let val y_1223_1545_1933 = (internal_copy_DTree x_1218_1540_1928) in (Node (x_1214_1536_1924 , x_1215_1537_1925, x_1216_1538_1926, y_1222_1544_1932, y_1223_1545_1933)) end end);

fun internal_print_DTree (arg_1239_1493_1893) = (case arg_1239_1493_1893 of Leaf (x_1240_1494_1894 , x_1241_1495_1895) => 
  let val wildcard_1244_1496_1896 = (print "(Leaf") in 
  let val wildcard_1247_1497_1897 = (print " ") in 
  let val y_1242_1498_1898 = (print(Int.toString(x_1240_1494_1894))) in 
  let val wildcard_1246_1499_1899 = (print " ") in 
  let val y_1243_1500_1900 = (print(Int.toString(x_1241_1495_1895))) in 
  let val wildcard_1245_1501_1901 = (print ")") in () end end end end end end 
  | Node (x_1248_1502_1902 , x_1249_1503_1903, x_1250_1504_1904, x_1251_1505_1905, x_1252_1506_1906) => 
  let val wildcard_1258_1507_1907 = (print "(Node") in 
  let val wildcard_1264_1508_1908 = (print " ") in 
  let val y_1253_1509_1909 = (print(Int.toString(x_1248_1502_1902))) in 
  let val wildcard_1263_1510_1910 = (print " ") in 
  let val y_1254_1511_1911 = (print(Int.toString(x_1249_1503_1903))) in 
  let val wildcard_1262_1512_1912 = (print " ") in 
  let val y_1255_1513_1913 = (print(Int.toString(x_1250_1504_1904))) in 
  let val wildcard_1261_1514_1914 = (print " ") in 
  let val y_1256_1515_1915 = (internal_print_DTree x_1251_1505_1905) in 
  let val wildcard_1260_1516_1916 = (print " ") in 
  let val y_1257_1517_1917 = (internal_print_DTree x_1252_1506_1906) in 
  let val wildcard_1259_1518_1918 = (print ")") in () end end end end end end end end end end end end);

fun generate_loop_927_1152 (vec_466_1484_1879 , idx_467_1485_1880, end_468_1486_1881, i_436_1487_1882) = 
  let val fltIf_1613_1883 = (idx_467_1485_1880 = end_468_1486_1881) in 
  (if fltIf_1613_1883 then vec_466_1484_1879 
   else 
  let val fltPrm_1617_1886 = (idx_467_1485_1880 * 3) in 
  let val fltPrm_1616_1887 = (fltPrm_1617_1886 + i_436_1487_1882) in 
  let val fltPrm_1618_1888 = 1 in 
  let val fltPrm_1615_1889 = (fltPrm_1616_1887 + fltPrm_1618_1888) in 
  let val fltPrm_1614_1890 = (fltPrm_1615_1889 mod 100) in 
  let val vec1_471_1488_1891 = let val _ = (ArraySlice.update(vec_466_1484_1879 , idx_467_1485_1880, fltPrm_1614_1890)) in vec_466_1484_1879 end in 
  let val fltAppE_1619_1892 = (idx_467_1485_1880 + 1) in (generate_loop_927_1152(vec1_471_1488_1891 , fltAppE_1619_1892, end_468_1486_1881, i_436_1487_1882)) end end end end end end end) end;

fun generate_loop_927_1151 (vec_466_1477_1865 , idx_467_1478_1866, end_468_1479_1867, n_416_1480_1868) = 
  let val fltIf_1606_1869 = (idx_467_1478_1866 = end_468_1479_1867) in 
  (if fltIf_1606_1869 then vec_466_1477_1865 
   else 
  let val fltPrm_1610_1872 = (idx_467_1478_1866 * 7) in 
  let val fltPrm_1609_1873 = (fltPrm_1610_1872 + n_416_1480_1868) in 
  let val fltPrm_1611_1874 = 1 in 
  let val fltPrm_1608_1875 = (fltPrm_1609_1873 + fltPrm_1611_1874) in 
  let val fltPrm_1607_1876 = (fltPrm_1608_1875 mod 100) in 
  let val vec1_471_1481_1877 = let val _ = (ArraySlice.update(vec_466_1477_1865 , idx_467_1478_1866, fltPrm_1607_1876)) in vec_466_1477_1865 end in 
  let val fltAppE_1612_1878 = (idx_467_1478_1866 + 1) in (generate_loop_927_1151(vec1_471_1481_1877 , fltAppE_1612_1878, end_468_1479_1867, n_416_1480_1868)) end end end end end end end) end;

fun countNodes (t_669_1469_1854) = (case t_669_1469_1854 of Leaf (wildcard__7_670_1470_1855 , wildcard__8_671_1471_1856) => 1 
  | Node (wildcard__11_672_1472_1857 , wildcard__12_673_1473_1858, wildcard__13_674_1474_1859, l_675_1475_1860, r_676_1476_1861) => 
  let val fltPrm_1604_1862 = (countNodes l_675_1475_1860) in 
  let val fltPrm_1603_1863 = (1 + fltPrm_1604_1862) in 
  let val fltPrm_1605_1864 = (countNodes r_676_1476_1861) in (fltPrm_1603_1863 + fltPrm_1605_1864) end end end);

fun classifyDepth (t_658_1458_1838 , fv_659_1459_1839, depth_660_1460_1840) = (case t_658_1458_1838 of Leaf (wildcard__158_661_1461_1841 , wildcard__159_662_1462_1842) => depth_660_1460_1840 
  | Node (feature_663_1463_1843 , threshold_664_1464_1844, wildcard__162_665_1465_1845, left_666_1466_1846, right_667_1467_1847) => 
  let val val_668_1468_1850 = (ArraySlice.sub(fv_659_1459_1839 , feature_663_1463_1843)) in 
  let val fltIf_1600_1851 = (val_668_1468_1850 <= threshold_664_1464_1844) in 
  (if fltIf_1600_1851 then 
  let val fltAppE_1601_1852 = (depth_660_1460_1840 + 1) in (classifyDepth(left_666_1466_1846 , fv_659_1459_1839, fltAppE_1601_1852)) end 
   else 
  let val fltAppE_1602_1853 = (depth_660_1460_1840 + 1) in (classifyDepth(right_667_1467_1847 , fv_659_1459_1839, fltAppE_1602_1853)) end) end end);

fun sumSamples (t_627_1440_1817) = (case t_627_1440_1817 of Leaf (wildcard__60_628_1441_1818 , samples_629_1442_1819) => samples_629_1442_1819 
  | Node (wildcard__63_630_1443_1820 , wildcard__64_631_1444_1821, wildcard__65_632_1445_1822, l_633_1446_1823, r_634_1447_1824) => 
  let val fltPrm_1597_1825 = (sumSamples l_633_1446_1823) in 
  let val fltPrm_1598_1826 = (sumSamples r_634_1447_1824) in (fltPrm_1597_1825 + fltPrm_1598_1826) end end);

fun internal_traverse_DTree (arg_1224_1430_1807) = (case arg_1224_1430_1807 of Leaf (x_1225_1431_1808 , x_1226_1432_1809) => () 
  | Node (x_1229_1433_1810 , x_1230_1434_1811, x_1231_1435_1812, x_1232_1436_1813, x_1233_1437_1814) => 
  let val y_1237_1438_1815 = (internal_traverse_DTree x_1232_1436_1813) in 
  let val y_1238_1439_1816 = (internal_traverse_DTree x_1233_1437_1814) in () end end);

fun countLeaves (t_573_1402_1786) = (case t_573_1402_1786 of Leaf (wildcard__20_574_1403_1787 , wildcard__21_575_1404_1788) => 1 
  | Node (wildcard__24_576_1405_1789 , wildcard__25_577_1406_1790, wildcard__26_578_1407_1791, l_579_1408_1792, r_580_1409_1793) => 
  let val fltPrm_1592_1794 = (countLeaves l_579_1408_1792) in 
  let val fltPrm_1593_1795 = (countLeaves r_580_1409_1793) in (fltPrm_1592_1794 + fltPrm_1593_1795) end end);

fun sumImpurity (t_522_1390_1775) = (case t_522_1390_1775 of Leaf (wildcard__48_523_1391_1776 , wildcard__49_524_1392_1777) => 0 
  | Node (wildcard__52_525_1393_1778 , wildcard__53_526_1394_1779, imp_527_1395_1780, l_528_1396_1781, r_529_1397_1782) => 
  let val fltPrm_1590_1783 = (sumImpurity l_528_1396_1781) in 
  let val fltPrm_1589_1784 = (imp_527_1395_1780 + fltPrm_1590_1783) in 
  let val fltPrm_1591_1785 = (sumImpurity r_529_1397_1782) in (fltPrm_1589_1784 + fltPrm_1591_1785) end end end);

fun countFeatureUses (fid_487_1377_1761 , t_488_1378_1762) = (case t_488_1378_1762 of Leaf (wildcard__73_489_1379_1763 , wildcard__74_490_1380_1764) => 0 
  | Node (f_491_1381_1765 , wildcard__77_492_1382_1766, wildcard__78_493_1383_1767, l_494_1384_1768, r_495_1385_1769) => 
  let val fltIf_1585_1770 = (f_491_1381_1765 = fid_487_1377_1761) in 
  let val here_496_1386_1771 = 
  (if fltIf_1585_1770 then 1 
   else 0) in 
  let val fltPrm_1587_1772 = (countFeatureUses(fid_487_1377_1761 , l_494_1384_1768)) in 
  let val fltPrm_1586_1773 = (here_496_1386_1771 + fltPrm_1587_1772) in 
  let val fltPrm_1588_1774 = (countFeatureUses(fid_487_1377_1761 , r_495_1385_1769)) in (fltPrm_1586_1773 + fltPrm_1588_1774) end end end end end);

fun buildTree (d_483_1373_1749) = 
  let val fltIf_1577_1750 = (d_483_1373_1749 <= 0) in 
  (if fltIf_1577_1750 then 
  let val fltPkd_1578_1751 = (d_483_1373_1749 mod 3) in 
  let val fltPrm_1580_1752 = (d_483_1373_1749 mod 10) in 
  let val fltPkd_1579_1753 = (1 + fltPrm_1580_1752) in (Leaf (fltPkd_1578_1751 , fltPkd_1579_1753)) end end end 
   else 
  let val feature_484_1374_1754 = (d_483_1373_1749 mod 16) in 
  let val threshold_485_1375_1755 = (d_483_1373_1749 mod 100) in 
  let val impurity_486_1376_1756 = (1000 - d_483_1373_1749) in 
  let val fltAppE_1582_1757 = (d_483_1373_1749 - 1) in 
  let val fltPkd_1581_1758 = (buildTree fltAppE_1582_1757) in 
  let val fltAppE_1584_1759 = (d_483_1373_1749 - 2) in 
  let val fltPkd_1583_1760 = (buildTree fltAppE_1584_1759) in (Node (feature_484_1374_1754 , threshold_485_1375_1755, impurity_486_1376_1756, fltPkd_1581_1758, fltPkd_1583_1760)) end end end end end end end) end;

fun maxInt (a_472_1369_1746 , b_473_1370_1747) = 
  let val fltIf_1576_1748 = (a_472_1369_1746 > b_473_1370_1747) in 
  (if fltIf_1576_1748 then a_472_1369_1746 
   else b_473_1370_1747) end;

fun countSmallLeaves (thresh_454_1360_1734 , t_455_1361_1735) = (case t_455_1361_1735 of Leaf (wildcard__100_456_1362_1736 , samples_457_1363_1737) => 
  let val fltIf_1573_1738 = (samples_457_1363_1737 < thresh_454_1360_1734) in 
  (if fltIf_1573_1738 then 1 
   else 0) end 
  | Node (wildcard__103_458_1364_1739 , wildcard__104_459_1365_1740, wildcard__105_460_1366_1741, l_461_1367_1742, r_462_1368_1743) => 
  let val fltPrm_1574_1744 = (countSmallLeaves(thresh_454_1360_1734 , l_461_1367_1742)) in 
  let val fltPrm_1575_1745 = (countSmallLeaves(thresh_454_1360_1734 , r_462_1368_1743)) in (fltPrm_1574_1744 + fltPrm_1575_1745) end end);

fun mkFeatureVec (n_416_1354_1715) = 
  let val n__421_1521_1550_1718 = (maxInt(n_416_1354_1715 , 0)) in 
  let val vec_422_1522_1551_1719 = ((fn internal__ => ArraySlice.full(Array.array(internal__, 0))) n__421_1521_1550_1718) in 
  let val vec1_423_1523_1552_1720 = (generate_loop_927_1151(vec_422_1522_1551_1719 , 0, n__421_1521_1550_1718, n_416_1354_1715)) in vec1_423_1523_1552_1720 end end end;

fun sumPathLengths (depth_405_1343_1702 , t_406_1344_1703) = (case t_406_1344_1703 of Leaf (wildcard__128_407_1345_1704 , samples_408_1346_1705) => (depth_405_1343_1702 * samples_408_1346_1705) 
  | Node (wildcard__131_409_1347_1706 , wildcard__132_410_1348_1707, wildcard__133_411_1349_1708, l_412_1350_1709, r_413_1351_1710) => 
  let val fltAppE_1568_1711 = (depth_405_1343_1702 + 1) in 
  let val dl_414_1352_1712 = (sumPathLengths(fltAppE_1568_1711 , l_412_1350_1709)) in 
  let val fltAppE_1569_1713 = (depth_405_1343_1702 + 1) in 
  let val dr_415_1353_1714 = (sumPathLengths(fltAppE_1569_1713 , r_413_1351_1710)) in (dl_414_1352_1712 + dr_415_1353_1714) end end end end);

fun classify (t_395_1333_1689 , fv_396_1334_1690) = (case t_395_1333_1689 of Leaf (label_397_1335_1691 , wildcard__145_398_1336_1692) => label_397_1335_1691 
  | Node (feature_399_1337_1693 , threshold_400_1338_1694, wildcard__148_401_1339_1695, left_402_1340_1696, right_403_1341_1697) => 
  let val val_404_1342_1700 = (ArraySlice.sub(fv_396_1334_1690 , feature_399_1337_1693)) in 
  let val fltIf_1567_1701 = (val_404_1342_1700 <= threshold_400_1338_1694) in 
  (if fltIf_1567_1701 then (classify(left_402_1340_1696 , fv_396_1334_1690)) 
   else (classify(right_403_1341_1697 , fv_396_1334_1690))) end end);

fun classifyBatch (t_434_1355_1721 , fvSize_435_1356_1722, i_436_1357_1723) = 
  let val fltIf_1570_1724 = (i_436_1357_1723 <= 0) in 
  (if fltIf_1570_1724 then 0 
   else 
  let val n__421_1526_1555_1727 = (maxInt(fvSize_435_1356_1722 , 0)) in 
  let val vec_422_1527_1556_1728 = ((fn internal__ => ArraySlice.full(Array.array(internal__, 0))) n__421_1526_1555_1727) in 
  let val vec1_423_1528_1557_1729 = (generate_loop_927_1152(vec_422_1527_1556_1728 , 0, n__421_1526_1555_1727, i_436_1357_1723)) in 
  let val label_439_1359_1731 = (classify(t_434_1355_1721 , vec1_423_1528_1557_1729)) in 
  let val fltAppE_1572_1732 = (i_436_1357_1723 - 1) in 
  let val fltPrm_1571_1733 = (classifyBatch(t_434_1355_1721 , fvSize_435_1356_1722, fltAppE_1572_1732)) in (label_439_1359_1731 + fltPrm_1571_1733) end end end end end end) end;

fun max (a_368_1329_1686 , b_369_1330_1687) = 
  let val fltIf_1566_1688 = (a_368_1329_1686 > b_369_1330_1687) in 
  (if fltIf_1566_1688 then a_368_1329_1686 
   else b_369_1330_1687) end;

fun inferenceCost (t_616_1419_1796) = (case t_616_1419_1796 of Leaf (wildcard__114_617_1420_1797 , wildcard__115_618_1421_1798) => 0 
  | Node (wildcard__118_619_1422_1799 , wildcard__119_620_1423_1800, wildcard__120_621_1424_1801, l_622_1425_1802, r_623_1426_1803) => 
  let val fltAppE_1595_1804 = (inferenceCost l_622_1425_1802) in 
  let val fltAppE_1596_1805 = (inferenceCost r_623_1426_1803) in 
  let val fltPrm_1594_1806 = (max(fltAppE_1595_1804 , fltAppE_1596_1805)) in (1 + fltPrm_1594_1806) end end end);

fun treeDepth (t_642_1448_1827) = (case t_642_1448_1827 of Leaf (wildcard__33_643_1449_1828 , wildcard__34_644_1450_1829) => 1 
  | Node (wildcard__37_645_1451_1830 , wildcard__38_646_1452_1831, wildcard__39_647_1453_1832, l_648_1454_1833, r_649_1455_1834) => 
  let val dl_650_1456_1835 = (treeDepth l_648_1454_1833) in 
  let val dr_651_1457_1836 = (treeDepth r_649_1455_1834) in 
  let val fltPrm_1599_1837 = (max(dl_650_1456_1835 , dr_651_1457_1836)) in (1 + fltPrm_1599_1837) end end end);
val _ = (case 
  let val wildcard__299_302_1265_1620 = (printsym "Running program Decision Tree: ") in 
  let val wildcard__297_303_1266_1621 = (printsym "NEWLINE") in 
  let val fltPrm_1565_1622 = (GibbonCompat.getSizeParam()) in 
  let val fltAppE_1564_1623 = (fltPrm_1565_1622 + 35) in 
  let val tree_304_1267_1624 = (buildTree fltAppE_1564_1623) in 
  let val wildcard__294_305_1268_1625 = (printsym "Running pass countNodes (fold, uses=2): ") in 
  let val wildcard__292_306_1269_1626 = (printsym "NEWLINE") in 
  let val nodes_307_1270_1627 = (iterate (fn () => countNodes tree_304_1267_1624)) in 
  let val wildcard__288_308_1271_1628 = (printsym "End") in 
  let val wildcard__286_309_1272_1629 = (printsym "NEWLINE") in 
  let val wildcard__284_310_1273_1630 = (printsym "Running pass countLeaves (fold, uses=2): ") in 
  let val wildcard__282_311_1274_1631 = (printsym "NEWLINE") in 
  let val leaves_312_1275_1632 = (iterate (fn () => countLeaves tree_304_1267_1624)) in 
  let val wildcard__278_313_1276_1633 = (printsym "End") in 
  let val wildcard__276_314_1277_1634 = (printsym "NEWLINE") in 
  let val wildcard__274_315_1278_1635 = (printsym "Running pass treeDepth (fold, uses=2): ") in 
  let val wildcard__272_316_1279_1636 = (printsym "NEWLINE") in 
  let val depth_317_1280_1637 = (iterate (fn () => treeDepth tree_304_1267_1624)) in 
  let val wildcard__268_318_1281_1638 = (printsym "End") in 
  let val wildcard__266_319_1282_1639 = (printsym "NEWLINE") in 
  let val wildcard__264_320_1283_1640 = (printsym "Running pass sumImpurity (fold, uses=3): ") in 
  let val wildcard__262_321_1284_1641 = (printsym "NEWLINE") in 
  let val imp_322_1285_1642 = (iterate (fn () => sumImpurity tree_304_1267_1624)) in 
  let val wildcard__258_323_1286_1643 = (printsym "End") in 
  let val wildcard__256_324_1287_1644 = (printsym "NEWLINE") in 
  let val wildcard__254_325_1288_1645 = (printsym "Running pass sumSamples (fold, uses=3): ") in 
  let val wildcard__252_326_1289_1646 = (printsym "NEWLINE") in 
  let val samples_327_1290_1647 = (iterate (fn () => sumSamples tree_304_1267_1624)) in 
  let val wildcard__248_328_1291_1648 = (printsym "End") in 
  let val wildcard__246_329_1292_1649 = (printsym "NEWLINE") in 
  let val wildcard__244_330_1293_1650 = (printsym "Running pass countFeatureUses (fold, uses=3): ") in 
  let val wildcard__242_331_1294_1651 = (printsym "NEWLINE") in 
  let val feat0_332_1295_1652 = (iterate (fn () => countFeatureUses(0 , tree_304_1267_1624))) in 
  let val wildcard__238_333_1296_1653 = (printsym "End") in 
  let val wildcard__236_334_1297_1654 = (printsym "NEWLINE") in 
  let val wildcard__234_335_1298_1655 = (printsym "Running pass countSmallLeaves (fold, uses=3): ") in 
  let val wildcard__232_336_1299_1656 = (printsym "NEWLINE") in 
  let val small_337_1300_1657 = (iterate (fn () => countSmallLeaves(5 , tree_304_1267_1624))) in 
  let val wildcard__228_338_1301_1658 = (printsym "End") in 
  let val wildcard__226_339_1302_1659 = (printsym "NEWLINE") in 
  let val wildcard__224_340_1303_1660 = (printsym "Running pass inferenceCost (fold, uses=2): ") in 
  let val wildcard__222_341_1304_1661 = (printsym "NEWLINE") in 
  let val cost_342_1305_1662 = (iterate (fn () => inferenceCost tree_304_1267_1624)) in 
  let val wildcard__218_343_1306_1663 = (printsym "End") in 
  let val wildcard__216_344_1307_1664 = (printsym "NEWLINE") in 
  let val wildcard__214_345_1308_1665 = (printsym "Running pass sumPathLengths (fold, uses=3): ") in 
  let val wildcard__212_346_1309_1666 = (printsym "NEWLINE") in 
  let val paths_347_1310_1667 = (iterate (fn () => sumPathLengths(0 , tree_304_1267_1624))) in 
  let val wildcard__208_348_1311_1668 = (printsym "End") in 
  let val wildcard__206_349_1312_1669 = (printsym "NEWLINE") in 
  let val fv_350_1313_1670 = (mkFeatureVec ((GibbonCompat.getSizeParam()) + 32)) in 
  let val wildcard__203_351_1314_1671 = (printsym "Running pass classify tree (fold, uses=5): ") in 
  let val wildcard__201_352_1315_1672 = (printsym "NEWLINE") in 
  let val pred_353_1316_1673 = (iterate (fn () => classify(tree_304_1267_1624 , fv_350_1313_1670))) in 
  let val wildcard__197_354_1317_1674 = (printsym "End") in 
  let val wildcard__195_355_1318_1675 = (printsym "NEWLINE") in 
  let val wildcard__193_356_1319_1676 = (printsym "Running pass classify Depth (fold, uses=4): ") in 
  let val wildcard__191_357_1320_1677 = (printsym "NEWLINE") in 
  let val pdepth_358_1321_1678 = (iterate (fn () => classifyDepth(tree_304_1267_1624 , fv_350_1313_1670, 0))) in 
  let val wildcard__187_359_1322_1679 = (printsym "End") in 
  let val wildcard__185_360_1323_1680 = (printsym "NEWLINE") in 
  let val wildcard__183_361_1324_1681 = (printsym "Running pass classify Batch (fold, uses=5): ") in 
  let val wildcard__181_362_1325_1682 = (printsym "NEWLINE") in 
  let val batch_363_1326_1683 = (iterate (fn () => classifyBatch(tree_304_1267_1624 , 32, 100))) in 
  let val wildcard__177_364_1327_1684 = (printsym "End") in 
  let val wildcard__175_365_1328_1685 = (printsym "NEWLINE") in (nodes_307_1270_1627 , leaves_312_1275_1632, depth_317_1280_1637, imp_322_1285_1642, samples_327_1290_1647, feat0_332_1295_1652, small_337_1300_1657, cost_342_1305_1662, paths_347_1310_1667, pred_353_1316_1673, pdepth_358_1321_1678, batch_363_1326_1683) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3, x__4, x__5, x__6, x__7, x__8, x__9, x__10, x__11, x__12) => let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print " "val _ = (print(Int.toString(x__4))) val _ = print " "val _ = (print(Int.toString(x__5))) val _ = print " "val _ = (print(Int.toString(x__6))) val _ = print " "val _ = (print(Int.toString(x__7))) val _ = print " "val _ = (print(Int.toString(x__8))) val _ = print " "val _ = (print(Int.toString(x__9))) val _ = print " "val _ = (print(Int.toString(x__10))) val _ = print " "val _ = (print(Int.toString(x__11))) val _ = print " "val _ = (print(Int.toString(x__12))) val _ = print ")" in () end);
val _ = print "\n"
