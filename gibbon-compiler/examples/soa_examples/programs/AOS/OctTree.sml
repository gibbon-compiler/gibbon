datatype dat_Octree = Cell of (int  * int * int * int * int *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree *  dat_Octree) | Particle of (int  * int * int)| EmptyOct ;

fun internal_copy_Octree (arg_1430_1976_2824) = (case arg_1430_1976_2824 of Cell (x_1431_1977_2825 , x_1432_1978_2826, x_1433_1979_2827, x_1434_1980_2828, x_1435_1981_2829, x_1436_1982_2830, x_1437_1983_2831, x_1438_1984_2832, x_1439_1985_2833, x_1440_1986_2834, x_1441_1987_2835, x_1442_1988_2836, x_1443_1989_2837) => 
  let val y_1449_1995_2843 = (internal_copy_Octree x_1436_1982_2830) in 
  let val y_1450_1996_2844 = (internal_copy_Octree x_1437_1983_2831) in 
  let val y_1451_1997_2845 = (internal_copy_Octree x_1438_1984_2832) in 
  let val y_1452_1998_2846 = (internal_copy_Octree x_1439_1985_2833) in 
  let val y_1453_1999_2847 = (internal_copy_Octree x_1440_1986_2834) in 
  let val y_1454_2000_2848 = (internal_copy_Octree x_1441_1987_2835) in 
  let val y_1455_2001_2849 = (internal_copy_Octree x_1442_1988_2836) in 
  let val y_1456_2002_2850 = (internal_copy_Octree x_1443_1989_2837) in (Cell (x_1431_1977_2825 , x_1432_1978_2826, x_1433_1979_2827, x_1434_1980_2828, x_1435_1981_2829, y_1449_1995_2843, y_1450_1996_2844, y_1451_1997_2845, y_1452_1998_2846, y_1453_1999_2847, y_1454_2000_2848, y_1455_2001_2849, y_1456_2002_2850)) end end end end end end end end 
  | Particle (x_1457_2003_2851 , x_1458_2004_2852, x_1459_2005_2853) => (Particle (x_1457_2003_2851 , x_1458_2004_2852, x_1459_2005_2853))
  | EmptyOct => EmptyOct);

fun internal_print_Octree (arg_1496_1921_2769) = (case arg_1496_1921_2769 of Cell (x_1497_1922_2770 , x_1498_1923_2771, x_1499_1924_2772, x_1500_1925_2773, x_1501_1926_2774, x_1502_1927_2775, x_1503_1928_2776, x_1504_1929_2777, x_1505_1930_2778, x_1506_1931_2779, x_1507_1932_2780, x_1508_1933_2781, x_1509_1934_2782) => 
  let val wildcard_1523_1935_2783 = (print "(Cell") in 
  let val wildcard_1537_1936_2784 = (print " ") in 
  let val y_1510_1937_2785 = (print(Int.toString(x_1497_1922_2770))) in 
  let val wildcard_1536_1938_2786 = (print " ") in 
  let val y_1511_1939_2787 = (print(Int.toString(x_1498_1923_2771))) in 
  let val wildcard_1535_1940_2788 = (print " ") in 
  let val y_1512_1941_2789 = (print(Int.toString(x_1499_1924_2772))) in 
  let val wildcard_1534_1942_2790 = (print " ") in 
  let val y_1513_1943_2791 = (print(Int.toString(x_1500_1925_2773))) in 
  let val wildcard_1533_1944_2792 = (print " ") in 
  let val y_1514_1945_2793 = (print(Int.toString(x_1501_1926_2774))) in 
  let val wildcard_1532_1946_2794 = (print " ") in 
  let val y_1515_1947_2795 = (internal_print_Octree x_1502_1927_2775) in 
  let val wildcard_1531_1948_2796 = (print " ") in 
  let val y_1516_1949_2797 = (internal_print_Octree x_1503_1928_2776) in 
  let val wildcard_1530_1950_2798 = (print " ") in 
  let val y_1517_1951_2799 = (internal_print_Octree x_1504_1929_2777) in 
  let val wildcard_1529_1952_2800 = (print " ") in 
  let val y_1518_1953_2801 = (internal_print_Octree x_1505_1930_2778) in 
  let val wildcard_1528_1954_2802 = (print " ") in 
  let val y_1519_1955_2803 = (internal_print_Octree x_1506_1931_2779) in 
  let val wildcard_1527_1956_2804 = (print " ") in 
  let val y_1520_1957_2805 = (internal_print_Octree x_1507_1932_2780) in 
  let val wildcard_1526_1958_2806 = (print " ") in 
  let val y_1521_1959_2807 = (internal_print_Octree x_1508_1933_2781) in 
  let val wildcard_1525_1960_2808 = (print " ") in 
  let val y_1522_1961_2809 = (internal_print_Octree x_1509_1934_2782) in 
  let val wildcard_1524_1962_2810 = (print ")") in () end end end end end end end end end end end end end end end end end end end end end end end end end end end end 
  | Particle (x_1538_1963_2811 , x_1539_1964_2812, x_1540_1965_2813) => 
  let val wildcard_1544_1966_2814 = (print "(Particle") in 
  let val wildcard_1548_1967_2815 = (print " ") in 
  let val y_1541_1968_2816 = (print(Int.toString(x_1538_1963_2811))) in 
  let val wildcard_1547_1969_2817 = (print " ") in 
  let val y_1542_1970_2818 = (print(Int.toString(x_1539_1964_2812))) in 
  let val wildcard_1546_1971_2819 = (print " ") in 
  let val y_1543_1972_2820 = (print(Int.toString(x_1540_1965_2813))) in 
  let val wildcard_1545_1973_2821 = (print ")") in () end end end end end end end end
  | EmptyOct => 
  let val wildcard_1549_1974_2822 = (print "(EmptyOct") in 
  let val wildcard_1550_1975_2823 = (print ")") in () end end);

fun momentumOf (t_805_1904_2752) = (case t_805_1904_2752 of Cell (wildcard__106_806_1905_2753 , wildcard__107_807_1906_2754, wildcard__108_808_1907_2755, wildcard__109_809_1908_2756, mom_810_1909_2757, wildcard__110_811_1910_2758, wildcard__111_812_1911_2759, wildcard__112_813_1912_2760, wildcard__113_814_1913_2761, wildcard__114_815_1914_2762, wildcard__115_816_1915_2763, wildcard__116_817_1916_2764, wildcard__117_818_1917_2765) => mom_810_1909_2757 
  | Particle (m_819_1918_2766 , wildcard__131_820_1919_2767, v_821_1920_2768) => (m_819_1918_2766 * v_821_1920_2768)
  | EmptyOct => 0);

fun sum8 (a_759_1858_2638 , b_760_1859_2639, c_761_1860_2640, d_762_1861_2641, e_763_1862_2642, f_764_1863_2643, g_765_1864_2644, h_766_1865_2645) = 
  let val fltPrm_2141_2646 = (a_759_1858_2638 + b_760_1859_2639) in 
  let val fltPrm_2140_2647 = (fltPrm_2141_2646 + c_761_1860_2640) in 
  let val fltPrm_2139_2648 = (fltPrm_2140_2647 + d_762_1861_2641) in 
  let val fltPrm_2138_2649 = (fltPrm_2139_2648 + e_763_1862_2642) in 
  let val fltPrm_2137_2650 = (fltPrm_2138_2649 + f_764_1863_2643) in 
  let val fltPrm_2136_2651 = (fltPrm_2137_2650 + g_765_1864_2644) in (fltPrm_2136_2651 + h_766_1865_2645) end end end end end end;

fun absI (x_758_1857_2636) = 
  let val fltIf_2135_2637 = (x_758_1857_2636 < 0) in 
  (if fltIf_2135_2637 then (0 - x_758_1857_2636) 
   else x_758_1857_2636) end;

fun fmmDownSeries (m_750_1849_2620 , mom_751_1850_2621, s_752_1851_2622, dist_753_1852_2623, order_754_1853_2624) = 
  let val fltIf_2127_2625 = (order_754_1853_2624 <= 0) in 
  (if fltIf_2127_2625 then 
  let val fltPrm_2128_2626 = (m_750_1849_2620 * 100) in (fltPrm_2128_2626 div dist_753_1852_2623) end 
   else 
  let val fltAppE_2129_2627 = (order_754_1853_2624 - 1) in 
  let val prev_755_1854_2628 = (fmmDownSeries(m_750_1849_2620 , mom_751_1850_2621, s_752_1851_2622, dist_753_1852_2623, fltAppE_2129_2627)) in 
  let val d_756_1855_2629 = (dist_753_1852_2623 + order_754_1853_2624) in 
  let val fltPrm_2131_2630 = (absI mom_751_1850_2621) in 
  let val fltPrm_2132_2631 = (s_752_1851_2622 * order_754_1853_2624) in 
  let val fltPrm_2130_2632 = (fltPrm_2131_2630 + fltPrm_2132_2631) in 
  let val fltPrm_2134_2633 = (d_756_1855_2629 * d_756_1855_2629) in 
  let val fltPrm_2133_2634 = (fltPrm_2134_2633 + 1) in 
  let val corr_757_1856_2635 = (fltPrm_2130_2632 div fltPrm_2133_2634) in (prev_755_1854_2628 + corr_757_1856_2635) end end end end end end end end end) end;

fun mixSeed (s_748_1847_2615 , salt_749_1848_2616) = 
  let val fltPrm_2125_2617 = (s_748_1847_2615 * 1103) in 
  let val fltPrm_2126_2618 = (salt_749_1848_2616 * 97) in 
  let val fltPrm_2124_2619 = (fltPrm_2125_2617 + fltPrm_2126_2618) in (fltPrm_2124_2619 + 13) end end end;

fun barnesHutPotential (t_723_1822_2572 , probe_724_1823_2573, theta_725_1824_2574) = (case t_723_1822_2572 of Cell (m_726_1825_2575 , c_727_1826_2576, n_728_1827_2577, s_729_1828_2578, wildcard__278_730_1829_2579, a_731_1830_2580, b_732_1831_2581, c1_733_1832_2582, d_734_1833_2583, e_735_1834_2584, f_736_1835_2585, g_737_1836_2586, h_738_1837_2587) => 
  let val fltAppE_2107_2588 = (c_727_1826_2576 - probe_724_1823_2573) in 
  let val fltPrm_2106_2589 = (absI fltAppE_2107_2588) in 
  let val dist_739_1838_2590 = (fltPrm_2106_2589 + 1) in 
  let val openLhs_740_1839_2591 = (s_729_1828_2578 * 100) in 
  let val openRhs_741_1840_2592 = (theta_725_1824_2574 * dist_739_1838_2590) in 
  let val fltIf_2108_2593 = (n_728_1827_2577 = 0) in 
  let val approx_742_1841_2596 = 
  (if fltIf_2108_2593 then 0 
   else 
  let val fltPrm_2109_2594 = (m_726_1825_2575 * 1000) in 
  let val fltPrm_2110_2595 = (dist_739_1838_2590 * dist_739_1838_2590) in (fltPrm_2109_2594 div fltPrm_2110_2595) end end) in 
  let val fltAppE_2111_2597 = (barnesHutPotential(a_731_1830_2580 , probe_724_1823_2573, theta_725_1824_2574)) in 
  let val fltAppE_2112_2598 = (barnesHutPotential(b_732_1831_2581 , probe_724_1823_2573, theta_725_1824_2574)) in 
  let val fltAppE_2113_2599 = (barnesHutPotential(c1_733_1832_2582 , probe_724_1823_2573, theta_725_1824_2574)) in 
  let val fltAppE_2114_2600 = (barnesHutPotential(d_734_1833_2583 , probe_724_1823_2573, theta_725_1824_2574)) in 
  let val fltAppE_2115_2601 = (barnesHutPotential(e_735_1834_2584 , probe_724_1823_2573, theta_725_1824_2574)) in 
  let val fltAppE_2116_2602 = (barnesHutPotential(f_736_1835_2585 , probe_724_1823_2573, theta_725_1824_2574)) in 
  let val fltAppE_2117_2603 = (barnesHutPotential(g_737_1836_2586 , probe_724_1823_2573, theta_725_1824_2574)) in 
  let val fltAppE_2118_2604 = (barnesHutPotential(h_738_1837_2587 , probe_724_1823_2573, theta_725_1824_2574)) in 
  let val recur_743_1842_2605 = (sum8(fltAppE_2111_2597 , fltAppE_2112_2598, fltAppE_2113_2599, fltAppE_2114_2600, fltAppE_2115_2601, fltAppE_2116_2602, fltAppE_2117_2603, fltAppE_2118_2604)) in 
  let val fltIf_2119_2606 = (openLhs_740_1839_2591 < openRhs_741_1840_2592) in 
  (if fltIf_2119_2606 then approx_742_1841_2596 
   else recur_743_1842_2605) end end end end end end end end end end end end end end end end end 
  | Particle (m_744_1843_2607 , p_745_1844_2608, wildcard__297_746_1845_2609) => 
  let val fltAppE_2121_2610 = (p_745_1844_2608 - probe_724_1823_2573) in 
  let val fltPrm_2120_2611 = (absI fltAppE_2121_2610) in 
  let val dist_747_1846_2612 = (fltPrm_2120_2611 + 1) in 
  let val fltPrm_2122_2613 = (m_744_1843_2607 * 1000) in 
  let val fltPrm_2123_2614 = (dist_747_1846_2612 * dist_747_1846_2612) in (fltPrm_2122_2613 div fltPrm_2123_2614) end end end end end
  | EmptyOct => 0);

fun sumMass (t_706_1805_2547) = (case t_706_1805_2547 of Cell (wildcard__176_707_1806_2548 , wildcard__177_708_1807_2549, wildcard__178_709_1808_2550, wildcard__179_710_1809_2551, wildcard__180_711_1810_2552, a_712_1811_2553, b_713_1812_2554, c_714_1813_2555, d_715_1814_2556, e_716_1815_2557, f_717_1816_2558, g_718_1817_2559, h_719_1818_2560) => 
  let val fltAppE_2098_2561 = (sumMass a_712_1811_2553) in 
  let val fltAppE_2099_2562 = (sumMass b_713_1812_2554) in 
  let val fltAppE_2100_2563 = (sumMass c_714_1813_2555) in 
  let val fltAppE_2101_2564 = (sumMass d_715_1814_2556) in 
  let val fltAppE_2102_2565 = (sumMass e_716_1815_2557) in 
  let val fltAppE_2103_2566 = (sumMass f_717_1816_2558) in 
  let val fltAppE_2104_2567 = (sumMass g_718_1817_2559) in 
  let val fltAppE_2105_2568 = (sumMass h_719_1818_2560) in (sum8(fltAppE_2098_2561 , fltAppE_2099_2562, fltAppE_2100_2563, fltAppE_2101_2564, fltAppE_2102_2565, fltAppE_2103_2566, fltAppE_2104_2567, fltAppE_2105_2568)) end end end end end end end end 
  | Particle (m_720_1819_2569 , wildcard__194_721_1820_2570, wildcard__195_722_1821_2571) => m_720_1819_2569
  | EmptyOct => 0);

fun clearFlags (t_660_1759_2470) = (case t_660_1759_2470 of Cell (m_661_1760_2471 , c_662_1761_2472, wildcard__369_663_1762_2473, s_664_1763_2474, mom_665_1764_2475, a_666_1765_2476, b_667_1766_2477, c1_668_1767_2478, d_669_1768_2479, e_670_1769_2480, f_671_1770_2481, g_672_1771_2482, h_673_1772_2483) => 
  let val fltPkd_2067_2484 = (clearFlags a_666_1765_2476) in 
  let val fltPkd_2068_2485 = (clearFlags b_667_1766_2477) in 
  let val fltPkd_2069_2486 = (clearFlags c1_668_1767_2478) in 
  let val fltPkd_2070_2487 = (clearFlags d_669_1768_2479) in 
  let val fltPkd_2071_2488 = (clearFlags e_670_1769_2480) in 
  let val fltPkd_2072_2489 = (clearFlags f_671_1770_2481) in 
  let val fltPkd_2073_2490 = (clearFlags g_672_1771_2482) in 
  let val fltPkd_2074_2491 = (clearFlags h_673_1772_2483) in (Cell (m_661_1760_2471 , c_662_1761_2472, 0, s_664_1763_2474, mom_665_1764_2475, fltPkd_2067_2484, fltPkd_2068_2485, fltPkd_2069_2486, fltPkd_2070_2487, fltPkd_2071_2488, fltPkd_2072_2489, fltPkd_2073_2490, fltPkd_2074_2491)) end end end end end end end end 
  | Particle (m_674_1773_2492 , p_675_1774_2493, v_676_1775_2494) => (Particle (m_674_1773_2492 , p_675_1774_2493, v_676_1775_2494))
  | EmptyOct => EmptyOct);

fun internal_traverse_Octree (arg_1463_1734_2445) = (case arg_1463_1734_2445 of Cell (x_1464_1735_2446 , x_1465_1736_2447, x_1466_1737_2448, x_1467_1738_2449, x_1468_1739_2450, x_1469_1740_2451, x_1470_1741_2452, x_1471_1742_2453, x_1472_1743_2454, x_1473_1744_2455, x_1474_1745_2456, x_1475_1746_2457, x_1476_1747_2458) => 
  let val y_1482_1748_2459 = (internal_traverse_Octree x_1469_1740_2451) in 
  let val y_1483_1749_2460 = (internal_traverse_Octree x_1470_1741_2452) in 
  let val y_1484_1750_2461 = (internal_traverse_Octree x_1471_1742_2453) in 
  let val y_1485_1751_2462 = (internal_traverse_Octree x_1472_1743_2454) in 
  let val y_1486_1752_2463 = (internal_traverse_Octree x_1473_1744_2455) in 
  let val y_1487_1753_2464 = (internal_traverse_Octree x_1474_1745_2456) in 
  let val y_1488_1754_2465 = (internal_traverse_Octree x_1475_1746_2457) in 
  let val y_1489_1755_2466 = (internal_traverse_Octree x_1476_1747_2458) in () end end end end end end end end 
  | Particle (x_1490_1756_2467 , x_1491_1757_2468, x_1492_1758_2469) => ()
  | EmptyOct => ());

fun scaleEnergy (t_640_1714_2414 , k_641_1715_2415) = (case t_640_1714_2414 of Cell (m_642_1716_2416 , c_643_1717_2417, n_644_1718_2418, s_645_1719_2419, mom_646_1720_2420, a_647_1721_2421, b_648_1722_2422, c1_649_1723_2423, d_650_1724_2424, e_651_1725_2425, f_652_1726_2426, g_653_1727_2427, h_654_1728_2428) => 
  let val fltPrm_2056_2429 = (mom_646_1720_2420 * k_641_1715_2415) in 
  let val fltPrm_2057_2430 = (s_645_1719_2419 + 1) in 
  let val mom__655_1729_2431 = (fltPrm_2056_2429 div fltPrm_2057_2430) in 
  let val fltPkd_2058_2432 = (scaleEnergy(a_647_1721_2421 , k_641_1715_2415)) in 
  let val fltPkd_2059_2433 = (scaleEnergy(b_648_1722_2422 , k_641_1715_2415)) in 
  let val fltPkd_2060_2434 = (scaleEnergy(c1_649_1723_2423 , k_641_1715_2415)) in 
  let val fltPkd_2061_2435 = (scaleEnergy(d_650_1724_2424 , k_641_1715_2415)) in 
  let val fltPkd_2062_2436 = (scaleEnergy(e_651_1725_2425 , k_641_1715_2415)) in 
  let val fltPkd_2063_2437 = (scaleEnergy(f_652_1726_2426 , k_641_1715_2415)) in 
  let val fltPkd_2064_2438 = (scaleEnergy(g_653_1727_2427 , k_641_1715_2415)) in 
  let val fltPkd_2065_2439 = (scaleEnergy(h_654_1728_2428 , k_641_1715_2415)) in (Cell (m_642_1716_2416 , c_643_1717_2417, n_644_1718_2418, s_645_1719_2419, mom__655_1729_2431, fltPkd_2058_2432, fltPkd_2059_2433, fltPkd_2060_2434, fltPkd_2061_2435, fltPkd_2062_2436, fltPkd_2063_2437, fltPkd_2064_2438, fltPkd_2065_2439)) end end end end end end end end end end end 
  | Particle (m_656_1730_2440 , p_657_1731_2441, v_658_1732_2442) => 
  let val fltPrm_2066_2443 = (v_658_1732_2442 * k_641_1715_2415) in 
  let val v__659_1733_2444 = (fltPrm_2066_2443 div 10) in (Particle (m_656_1730_2440 , p_657_1731_2441, v__659_1733_2444)) end end
  | EmptyOct => EmptyOct);

fun massOf (t_623_1697_2397) = (case t_623_1697_2397 of Cell (m_624_1698_2398 , wildcard__14_625_1699_2399, wildcard__15_626_1700_2400, wildcard__16_627_1701_2401, wildcard__17_628_1702_2402, wildcard__18_629_1703_2403, wildcard__19_630_1704_2404, wildcard__20_631_1705_2405, wildcard__21_632_1706_2406, wildcard__22_633_1707_2407, wildcard__23_634_1708_2408, wildcard__24_635_1709_2409, wildcard__25_636_1710_2410) => m_624_1698_2398 
  | Particle (m_637_1711_2411 , wildcard__39_638_1712_2412, wildcard__40_639_1713_2413) => m_637_1711_2411
  | EmptyOct => 0);

fun weightedPos (t_606_1680_2380) = (case t_606_1680_2380 of Cell (m_607_1681_2381 , c_608_1682_2382, wildcard__45_609_1683_2383, wildcard__46_610_1684_2384, wildcard__47_611_1685_2385, wildcard__48_612_1686_2386, wildcard__49_613_1687_2387, wildcard__50_614_1688_2388, wildcard__51_615_1689_2389, wildcard__52_616_1690_2390, wildcard__53_617_1691_2391, wildcard__54_618_1692_2392, wildcard__55_619_1693_2393) => (m_607_1681_2381 * c_608_1682_2382) 
  | Particle (m_620_1694_2394 , p_621_1695_2395, wildcard__69_622_1696_2396) => (m_620_1694_2394 * p_621_1695_2395)
  | EmptyOct => 0);

fun fmmUpSeries (m_601_1675_2370 , dip_602_1676_2371, order_603_1677_2372) = 
  let val fltIf_2051_2373 = (order_603_1677_2372 <= 0) in 
  (if fltIf_2051_2373 then (m_601_1675_2370 * 100) 
   else 
  let val fltAppE_2052_2374 = (order_603_1677_2372 - 1) in 
  let val prev_604_1678_2375 = (fmmUpSeries(m_601_1675_2370 , dip_602_1676_2371, fltAppE_2052_2374)) in 
  let val fltPrm_2053_2376 = (absI dip_602_1676_2371) in 
  let val fltPrm_2055_2377 = (order_603_1677_2372 * 20) in 
  let val fltPrm_2054_2378 = (fltPrm_2055_2377 + 1) in 
  let val corr_605_1679_2379 = (fltPrm_2053_2376 div fltPrm_2054_2378) in (prev_604_1678_2375 + corr_605_1679_2379) end end end end end end) end;

fun fmmPotential (t_677_1776_2495 , probe_678_1777_2496, order_679_1778_2497, eta_680_1779_2498) = (case t_677_1776_2495 of Cell (m_681_1780_2499 , c_682_1781_2500, wildcard__319_683_1782_2501, s_684_1783_2502, mom_685_1784_2503, a_686_1785_2504, b_687_1786_2505, c1_688_1787_2506, d_689_1788_2507, e_690_1789_2508, f_691_1790_2509, g_692_1791_2510, h_693_1792_2511) => 
  let val fltAppE_2076_2512 = (c_682_1781_2500 - probe_678_1777_2496) in 
  let val fltPrm_2075_2513 = (absI fltAppE_2076_2512) in 
  let val dist_694_1793_2514 = (fltPrm_2075_2513 + 1) in 
  let val farLhs_695_1794_2515 = (s_684_1783_2502 * 100) in 
  let val farRhs_696_1795_2516 = (eta_680_1779_2498 * dist_694_1793_2514) in 
  let val fltAppE_2077_2517 = (m_681_1780_2499 * c_682_1781_2500) in 
  let val upMoment_697_1796_2518 = (fmmUpSeries(m_681_1780_2499 , fltAppE_2077_2517, order_679_1778_2497)) in 
  let val downApprox_698_1797_2519 = (fmmDownSeries(m_681_1780_2499 , mom_685_1784_2503, s_684_1783_2502, dist_694_1793_2514, order_679_1778_2497)) in 
  let val fltPrm_2079_2520 = (dist_694_1793_2514 + 1) in 
  let val fltPrm_2078_2521 = (upMoment_697_1796_2518 div fltPrm_2079_2520) in 
  let val approx_699_1798_2522 = (fltPrm_2078_2521 + downApprox_698_1797_2519) in 
  let val fltAppE_2080_2523 = (fmmPotential(a_686_1785_2504 , probe_678_1777_2496, order_679_1778_2497, eta_680_1779_2498)) in 
  let val fltAppE_2081_2524 = (fmmPotential(b_687_1786_2505 , probe_678_1777_2496, order_679_1778_2497, eta_680_1779_2498)) in 
  let val fltAppE_2082_2525 = (fmmPotential(c1_688_1787_2506 , probe_678_1777_2496, order_679_1778_2497, eta_680_1779_2498)) in 
  let val fltAppE_2083_2526 = (fmmPotential(d_689_1788_2507 , probe_678_1777_2496, order_679_1778_2497, eta_680_1779_2498)) in 
  let val fltAppE_2084_2527 = (fmmPotential(e_690_1789_2508 , probe_678_1777_2496, order_679_1778_2497, eta_680_1779_2498)) in 
  let val fltAppE_2085_2528 = (fmmPotential(f_691_1790_2509 , probe_678_1777_2496, order_679_1778_2497, eta_680_1779_2498)) in 
  let val fltAppE_2086_2529 = (fmmPotential(g_692_1791_2510 , probe_678_1777_2496, order_679_1778_2497, eta_680_1779_2498)) in 
  let val fltAppE_2087_2530 = (fmmPotential(h_693_1792_2511 , probe_678_1777_2496, order_679_1778_2497, eta_680_1779_2498)) in 
  let val recur_700_1799_2531 = (sum8(fltAppE_2080_2523 , fltAppE_2081_2524, fltAppE_2082_2525, fltAppE_2083_2526, fltAppE_2084_2527, fltAppE_2085_2528, fltAppE_2086_2529, fltAppE_2087_2530)) in 
  let val fltIf_2088_2532 = (farLhs_695_1794_2515 < farRhs_696_1795_2516) in 
  (if fltIf_2088_2532 then approx_699_1798_2522 
   else recur_700_1799_2531) end end end end end end end end end end end end end end end end end end end end end 
  | Particle (m_701_1800_2533 , p_702_1801_2534, v_703_1802_2535) => 
  let val fltAppE_2090_2536 = (p_702_1801_2534 - probe_678_1777_2496) in 
  let val fltPrm_2089_2537 = (absI fltAppE_2090_2536) in 
  let val dist_704_1803_2538 = (fltPrm_2089_2537 + 1) in 
  let val fltAppE_2091_2539 = (m_701_1800_2533 * p_702_1801_2534) in 
  let val up_705_1804_2540 = (fmmUpSeries(m_701_1800_2533 , fltAppE_2091_2539, order_679_1778_2497)) in 
  let val fltPrm_2093_2541 = (dist_704_1803_2538 + 1) in 
  let val fltPrm_2092_2542 = (up_705_1804_2540 div fltPrm_2093_2541) in 
  let val fltPrm_2096_2543 = (m_701_1800_2533 * 100) in 
  let val fltPrm_2097_2544 = (absI v_703_1802_2535) in 
  let val fltPrm_2095_2545 = (fltPrm_2096_2543 + fltPrm_2097_2544) in 
  let val fltPrm_2094_2546 = (fltPrm_2095_2545 div dist_704_1803_2538) in (fltPrm_2092_2542 + fltPrm_2094_2546) end end end end end end end end end end end
  | EmptyOct => 0);

fun countActive (t_578_1652_2335 , theta_579_1653_2336) = (case t_578_1652_2335 of Cell (wildcard__223_580_1654_2337 , c_581_1655_2338, wildcard__224_582_1656_2339, s_583_1657_2340, wildcard__225_584_1658_2341, a_585_1659_2342, b_586_1660_2343, c1_587_1661_2344, d_588_1662_2345, e_589_1663_2346, f_590_1664_2347, g_591_1665_2348, h_592_1666_2349) => 
  let val fltAppE_2040_2351 = (c_581_1655_2338 - 0) in 
  let val fltPrm_2039_2352 = (absI fltAppE_2040_2351) in 
  let val dist_594_1668_2353 = (fltPrm_2039_2352 + 1) in 
  let val openLhs_595_1669_2354 = (s_583_1657_2340 * 100) in 
  let val openRhs_596_1670_2355 = (theta_579_1653_2336 * dist_594_1668_2353) in 
  let val fltIf_2041_2356 = (openLhs_595_1669_2354 >= openRhs_596_1670_2355) in 
  let val refine_597_1671_2357 = 
  (if fltIf_2041_2356 then 1 
   else 0) in 
  let val fltAppE_2043_2358 = (countActive(a_585_1659_2342 , theta_579_1653_2336)) in 
  let val fltAppE_2044_2359 = (countActive(b_586_1660_2343 , theta_579_1653_2336)) in 
  let val fltAppE_2045_2360 = (countActive(c1_587_1661_2344 , theta_579_1653_2336)) in 
  let val fltAppE_2046_2361 = (countActive(d_588_1662_2345 , theta_579_1653_2336)) in 
  let val fltAppE_2047_2362 = (countActive(e_589_1663_2346 , theta_579_1653_2336)) in 
  let val fltAppE_2048_2363 = (countActive(f_590_1664_2347 , theta_579_1653_2336)) in 
  let val fltAppE_2049_2364 = (countActive(g_591_1665_2348 , theta_579_1653_2336)) in 
  let val fltAppE_2050_2365 = (countActive(h_592_1666_2349 , theta_579_1653_2336)) in 
  let val fltPrm_2042_2366 = (sum8(fltAppE_2043_2358 , fltAppE_2044_2359, fltAppE_2045_2360, fltAppE_2046_2361, fltAppE_2047_2362, fltAppE_2048_2363, fltAppE_2049_2364, fltAppE_2050_2365)) in (refine_597_1671_2357 + fltPrm_2042_2366) end end end end end end end end end end end end end end end end 
  | Particle (wildcard__244_598_1672_2367 , wildcard__245_599_1673_2368, wildcard__246_600_1674_2369) => 0
  | EmptyOct => 0);

fun countParticles (t_561_1635_2310) = (case t_561_1635_2310 of Particle (wildcard__251_562_1636_2311 , wildcard__252_563_1637_2312, wildcard__253_564_1638_2313) => 1 
  | Cell (wildcard__257_565_1639_2314 , wildcard__258_566_1640_2315, wildcard__259_567_1641_2316, wildcard__260_568_1642_2317, wildcard__261_569_1643_2318, a_570_1644_2319, b_571_1645_2320, c_572_1646_2321, d_573_1647_2322, e_574_1648_2323, f_575_1649_2324, g_576_1650_2325, h_577_1651_2326) => 
  let val fltAppE_2031_2327 = (countParticles a_570_1644_2319) in 
  let val fltAppE_2032_2328 = (countParticles b_571_1645_2320) in 
  let val fltAppE_2033_2329 = (countParticles c_572_1646_2321) in 
  let val fltAppE_2034_2330 = (countParticles d_573_1647_2322) in 
  let val fltAppE_2035_2331 = (countParticles e_574_1648_2323) in 
  let val fltAppE_2036_2332 = (countParticles f_575_1649_2324) in 
  let val fltAppE_2037_2333 = (countParticles g_576_1650_2325) in 
  let val fltAppE_2038_2334 = (countParticles h_577_1651_2326) in (sum8(fltAppE_2031_2327 , fltAppE_2032_2328, fltAppE_2033_2329, fltAppE_2034_2330, fltAppE_2035_2331, fltAppE_2036_2332, fltAppE_2037_2333, fltAppE_2038_2334)) end end end end end end end end
  | EmptyOct => 0);

fun countOf (t_544_1618_2293) = (case t_544_1618_2293 of Cell (wildcard__74_545_1619_2294 , wildcard__75_546_1620_2295, n_547_1621_2296, wildcard__76_548_1622_2297, wildcard__77_549_1623_2298, wildcard__78_550_1624_2299, wildcard__79_551_1625_2300, wildcard__80_552_1626_2301, wildcard__81_553_1627_2302, wildcard__82_554_1628_2303, wildcard__83_555_1629_2304, wildcard__84_556_1630_2305, wildcard__85_557_1631_2306) => n_547_1621_2296 
  | Particle (wildcard__99_558_1632_2307 , wildcard__100_559_1633_2308, wildcard__101_560_1634_2309) => 1
  | EmptyOct => 0);

fun maxI (a_542_1616_2290 , b_543_1617_2291) = 
  let val fltIf_2030_2292 = (a_542_1616_2290 > b_543_1617_2291) in 
  (if fltIf_2030_2292 then a_542_1616_2290 
   else b_543_1617_2291) end;

fun buildOctree (d_767_1866_2652 , seed_768_1867_2653, center_769_1868_2654, half_770_1869_2655) = 
  let val fltIf_2142_2656 = (d_767_1866_2652 = 0) in 
  (if fltIf_2142_2656 then 
  let val fltPrm_2144_2657 = (absI seed_768_1867_2653) in 
  let val fltPrm_2143_2658 = (fltPrm_2144_2657 mod 5) in 
  let val m_771_1870_2659 = (1 + fltPrm_2143_2658) in 
  let val fltPrm_2147_2660 = (mixSeed(seed_768_1867_2653 , 3)) in 
  let val fltPrm_2146_2661 = (fltPrm_2147_2660 mod 3) in 
  let val fltPrm_2145_2662 = (center_769_1868_2654 + fltPrm_2146_2661) in 
  let val p_772_1871_2663 = (fltPrm_2145_2662 - 1) in 
  let val fltPrm_2149_2664 = (mixSeed(seed_768_1867_2653 , 11)) in 
  let val fltPrm_2148_2665 = (fltPrm_2149_2664 mod 11) in 
  let val v_773_1872_2666 = (fltPrm_2148_2665 - 5) in (Particle (m_771_1870_2659 , p_772_1871_2663, v_773_1872_2666)) end end end end end end end end end end 
   else 
  let val fltAppE_2150_2667 = (half_770_1869_2655 div 2) in 
  let val half__774_1873_2668 = (maxI(1 , fltAppE_2150_2667)) in 
  let val fltAppE_2151_2669 = (half_770_1869_2655 div 4) in 
  let val stride_775_1874_2670 = (maxI(1 , fltAppE_2151_2669)) in 
  let val fltPrm_2152_2671 = (stride_775_1874_2670 * 7) in 
  let val o0_776_1875_2672 = (0 - fltPrm_2152_2671) in 
  let val fltPrm_2153_2673 = (stride_775_1874_2670 * 5) in 
  let val o1_777_1876_2674 = (0 - fltPrm_2153_2673) in 
  let val fltPrm_2154_2675 = (stride_775_1874_2670 * 3) in 
  let val o2_778_1877_2676 = (0 - fltPrm_2154_2675) in 
  let val o3_779_1878_2677 = (0 - stride_775_1874_2670) in 
  let val o5_781_1880_2679 = (stride_775_1874_2670 * 3) in 
  let val o6_782_1881_2680 = (stride_775_1874_2670 * 5) in 
  let val o7_783_1882_2681 = (stride_775_1874_2670 * 7) in 
  let val fltAppE_2155_2682 = (d_767_1866_2652 - 1) in 
  let val fltAppE_2156_2683 = (mixSeed(seed_768_1867_2653 , 1)) in 
  let val fltAppE_2157_2684 = (center_769_1868_2654 + o0_776_1875_2672) in 
  let val c0_784_1883_2685 = (buildOctree(fltAppE_2155_2682 , fltAppE_2156_2683, fltAppE_2157_2684, half__774_1873_2668)) in 
  let val fltAppE_2158_2686 = (d_767_1866_2652 - 1) in 
  let val fltAppE_2159_2687 = (mixSeed(seed_768_1867_2653 , 2)) in 
  let val fltAppE_2160_2688 = (center_769_1868_2654 + o1_777_1876_2674) in 
  let val c1_785_1884_2689 = (buildOctree(fltAppE_2158_2686 , fltAppE_2159_2687, fltAppE_2160_2688, half__774_1873_2668)) in 
  let val fltAppE_2161_2690 = (d_767_1866_2652 - 1) in 
  let val fltAppE_2162_2691 = (mixSeed(seed_768_1867_2653 , 3)) in 
  let val fltAppE_2163_2692 = (center_769_1868_2654 + o2_778_1877_2676) in 
  let val c2_786_1885_2693 = (buildOctree(fltAppE_2161_2690 , fltAppE_2162_2691, fltAppE_2163_2692, half__774_1873_2668)) in 
  let val fltAppE_2164_2694 = (d_767_1866_2652 - 1) in 
  let val fltAppE_2165_2695 = (mixSeed(seed_768_1867_2653 , 4)) in 
  let val fltAppE_2166_2696 = (center_769_1868_2654 + o3_779_1878_2677) in 
  let val c3_787_1886_2697 = (buildOctree(fltAppE_2164_2694 , fltAppE_2165_2695, fltAppE_2166_2696, half__774_1873_2668)) in 
  let val fltAppE_2167_2698 = (d_767_1866_2652 - 1) in 
  let val fltAppE_2168_2699 = (mixSeed(seed_768_1867_2653 , 5)) in 
  let val fltAppE_2169_2700 = (center_769_1868_2654 + stride_775_1874_2670) in 
  let val c4_788_1887_2701 = (buildOctree(fltAppE_2167_2698 , fltAppE_2168_2699, fltAppE_2169_2700, half__774_1873_2668)) in 
  let val fltAppE_2170_2702 = (d_767_1866_2652 - 1) in 
  let val fltAppE_2171_2703 = (mixSeed(seed_768_1867_2653 , 6)) in 
  let val fltAppE_2172_2704 = (center_769_1868_2654 + o5_781_1880_2679) in 
  let val c5_789_1888_2705 = (buildOctree(fltAppE_2170_2702 , fltAppE_2171_2703, fltAppE_2172_2704, half__774_1873_2668)) in 
  let val fltAppE_2173_2706 = (d_767_1866_2652 - 1) in 
  let val fltAppE_2174_2707 = (mixSeed(seed_768_1867_2653 , 7)) in 
  let val fltAppE_2175_2708 = (center_769_1868_2654 + o6_782_1881_2680) in 
  let val c6_790_1889_2709 = (buildOctree(fltAppE_2173_2706 , fltAppE_2174_2707, fltAppE_2175_2708, half__774_1873_2668)) in 
  let val fltAppE_2176_2710 = (d_767_1866_2652 - 1) in 
  let val fltAppE_2177_2711 = (mixSeed(seed_768_1867_2653 , 8)) in 
  let val fltAppE_2178_2712 = (center_769_1868_2654 + o7_783_1882_2681) in 
  let val c7_791_1890_2713 = (buildOctree(fltAppE_2176_2710 , fltAppE_2177_2711, fltAppE_2178_2712, half__774_1873_2668)) in 
  let val m0_792_1891_2714 = (massOf c0_784_1883_2685) in 
  let val m1_793_1892_2715 = (massOf c1_785_1884_2689) in 
  let val m2_794_1893_2716 = (massOf c2_786_1885_2693) in 
  let val m3_795_1894_2717 = (massOf c3_787_1886_2697) in 
  let val m4_796_1895_2718 = (massOf c4_788_1887_2701) in 
  let val m5_797_1896_2719 = (massOf c5_789_1888_2705) in 
  let val m6_798_1897_2720 = (massOf c6_790_1889_2709) in 
  let val m7_799_1898_2721 = (massOf c7_791_1890_2713) in 
  let val mTot_800_1899_2722 = (sum8(m0_792_1891_2714 , m1_793_1892_2715, m2_794_1893_2716, m3_795_1894_2717, m4_796_1895_2718, m5_797_1896_2719, m6_798_1897_2720, m7_799_1898_2721)) in 
  let val fltAppE_2179_2723 = (weightedPos c0_784_1883_2685) in 
  let val fltAppE_2180_2724 = (weightedPos c1_785_1884_2689) in 
  let val fltAppE_2181_2725 = (weightedPos c2_786_1885_2693) in 
  let val fltAppE_2182_2726 = (weightedPos c3_787_1886_2697) in 
  let val fltAppE_2183_2727 = (weightedPos c4_788_1887_2701) in 
  let val fltAppE_2184_2728 = (weightedPos c5_789_1888_2705) in 
  let val fltAppE_2185_2729 = (weightedPos c6_790_1889_2709) in 
  let val fltAppE_2186_2730 = (weightedPos c7_791_1890_2713) in 
  let val wTot_801_1900_2731 = (sum8(fltAppE_2179_2723 , fltAppE_2180_2724, fltAppE_2181_2725, fltAppE_2182_2726, fltAppE_2183_2727, fltAppE_2184_2728, fltAppE_2185_2729, fltAppE_2186_2730)) in 
  let val fltAppE_2187_2732 = (countOf c0_784_1883_2685) in 
  let val fltAppE_2188_2733 = (countOf c1_785_1884_2689) in 
  let val fltAppE_2189_2734 = (countOf c2_786_1885_2693) in 
  let val fltAppE_2190_2735 = (countOf c3_787_1886_2697) in 
  let val fltAppE_2191_2736 = (countOf c4_788_1887_2701) in 
  let val fltAppE_2192_2737 = (countOf c5_789_1888_2705) in 
  let val fltAppE_2193_2738 = (countOf c6_790_1889_2709) in 
  let val fltAppE_2194_2739 = (countOf c7_791_1890_2713) in 
  let val nTot_802_1901_2740 = (sum8(fltAppE_2187_2732 , fltAppE_2188_2733, fltAppE_2189_2734, fltAppE_2190_2735, fltAppE_2191_2736, fltAppE_2192_2737, fltAppE_2193_2738, fltAppE_2194_2739)) in 
  let val fltAppE_2195_2741 = (momentumOf c0_784_1883_2685) in 
  let val fltAppE_2196_2742 = (momentumOf c1_785_1884_2689) in 
  let val fltAppE_2197_2743 = (momentumOf c2_786_1885_2693) in 
  let val fltAppE_2198_2744 = (momentumOf c3_787_1886_2697) in 
  let val fltAppE_2199_2745 = (momentumOf c4_788_1887_2701) in 
  let val fltAppE_2200_2746 = (momentumOf c5_789_1888_2705) in 
  let val fltAppE_2201_2747 = (momentumOf c6_790_1889_2709) in 
  let val fltAppE_2202_2748 = (momentumOf c7_791_1890_2713) in 
  let val pTot_803_1902_2749 = (sum8(fltAppE_2195_2741 , fltAppE_2196_2742, fltAppE_2197_2743, fltAppE_2198_2744, fltAppE_2199_2745, fltAppE_2200_2746, fltAppE_2201_2747, fltAppE_2202_2748)) in 
  let val fltIf_2203_2750 = (mTot_800_1899_2722 = 0) in 
  let val com_804_1903_2751 = 
  (if fltIf_2203_2750 then center_769_1868_2654 
   else (wTot_801_1900_2731 div mTot_800_1899_2722)) in (Cell (mTot_800_1899_2722 , com_804_1903_2751, nTot_802_1901_2740, half_770_1869_2655, pTot_803_1902_2749, c0_784_1883_2685, c1_785_1884_2689, c2_786_1885_2693, c3_787_1886_2697, c4_788_1887_2701, c5_789_1888_2705, c6_790_1889_2709, c7_791_1890_2713)) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end) end;

fun sumEnergy (t_522_1596_2251) = (case t_522_1596_2251 of Cell (m_523_1597_2252 , c_524_1598_2253, wildcard__200_525_1599_2254, s_526_1600_2255, mom_527_1601_2256, a_528_1602_2257, b_529_1603_2258, c1_530_1604_2259, d_531_1605_2260, e_532_1606_2261, f_533_1607_2262, g_534_1608_2263, h_535_1609_2264) => 
  let val fltPrm_2011_2265 = (absI c_524_1598_2253) in 
  let val dist_536_1610_2266 = (fltPrm_2011_2265 + 1) in 
  let val fltPrm_2013_2267 = (m_523_1597_2252 * mom_527_1601_2256) in 
  let val fltPrm_2012_2268 = (fltPrm_2013_2267 * mom_527_1601_2256) in 
  let val fltPrm_2015_2269 = (m_523_1597_2252 * m_523_1597_2252) in 
  let val fltPrm_2014_2270 = (fltPrm_2015_2269 + 1) in 
  let val bulk_537_1611_2271 = (fltPrm_2012_2268 div fltPrm_2014_2270) in 
  let val fltPrm_2017_2272 = (m_523_1597_2252 * s_526_1600_2255) in 
  let val fltPrm_2016_2273 = (fltPrm_2017_2272 * 50) in 
  let val pot_538_1612_2274 = (fltPrm_2016_2273 div dist_536_1610_2266) in 
  let val fltPrm_2018_2275 = (bulk_537_1611_2271 + pot_538_1612_2274) in 
  let val fltAppE_2020_2276 = (sumEnergy a_528_1602_2257) in 
  let val fltAppE_2021_2277 = (sumEnergy b_529_1603_2258) in 
  let val fltAppE_2022_2278 = (sumEnergy c1_530_1604_2259) in 
  let val fltAppE_2023_2279 = (sumEnergy d_531_1605_2260) in 
  let val fltAppE_2024_2280 = (sumEnergy e_532_1606_2261) in 
  let val fltAppE_2025_2281 = (sumEnergy f_533_1607_2262) in 
  let val fltAppE_2026_2282 = (sumEnergy g_534_1608_2263) in 
  let val fltAppE_2027_2283 = (sumEnergy h_535_1609_2264) in 
  let val fltPrm_2019_2284 = (sum8(fltAppE_2020_2276 , fltAppE_2021_2277, fltAppE_2022_2278, fltAppE_2023_2279, fltAppE_2024_2280, fltAppE_2025_2281, fltAppE_2026_2282, fltAppE_2027_2283)) in (fltPrm_2018_2275 + fltPrm_2019_2284) end end end end end end end end end end end end end end end end end end end end 
  | Particle (m_539_1613_2285 , wildcard__217_540_1614_2286, v_541_1615_2287) => 
  let val fltPrm_2029_2288 = (m_539_1613_2285 * v_541_1615_2287) in 
  let val fltPrm_2028_2289 = (fltPrm_2029_2288 * v_541_1615_2287) in (fltPrm_2028_2289 div 2) end end
  | EmptyOct => 0);
val _ = (case 
  let val wildcard__474_477_1551_2204 = (print "Running program OctTree Physics Simulation: ") in 
  let val wildcard__472_478_1552_2205 = (print "NEWLINE") in 
  let val fltPrm_2010_2206 = 1 in 
  let val fltAppE_2009_2207 = (fltPrm_2010_2206 + 7) in 
  let val octTree_479_1553_2208 = (buildOctree(fltAppE_2009_2207 , 17, 0, 64)) in 
  let val wildcard__469_480_1554_2209 = (print "Running pass sumMass (fold, uses=10): ") in 
  let val wildcard__467_481_1555_2210 = (print "NEWLINE") in 
  let val totMass_482_1556_2211 = (sumMass octTree_479_1553_2208) in 
  let val wildcard__463_483_1557_2212 = (print "End") in 
  let val wildcard__461_484_1558_2213 = (print "NEWLINE") in 
  let val wildcard__459_485_1559_2214 = (print "Running pass sumEnergy (fold, uses=12): ") in 
  let val wildcard__457_486_1560_2215 = (print "NEWLINE") in 
  let val totEnergy_487_1561_2216 = (sumEnergy octTree_479_1553_2208) in 
  let val wildcard__453_488_1562_2217 = (print "End") in 
  let val wildcard__451_489_1563_2218 = (print "NEWLINE") in 
  let val wildcard__449_490_1564_2219 = (print "Running pass countActive (fold, uses=10): ") in 
  let val wildcard__447_491_1565_2220 = (print "NEWLINE") in 
  let val totActive_492_1566_2221 = (countActive(octTree_479_1553_2208 , 60)) in 
  let val wildcard__443_493_1567_2222 = (print "End") in 
  let val wildcard__441_494_1568_2223 = (print "NEWLINE") in 
  let val wildcard__439_495_1569_2224 = (print "Running pass countParticles (fold, uses=8): ") in 
  let val wildcard__437_496_1570_2225 = (print "NEWLINE") in 
  let val totParticles_497_1571_2226 = (countParticles octTree_479_1553_2208) in 
  let val wildcard__433_498_1572_2227 = (print "End") in 
  let val wildcard__431_499_1573_2228 = (print "NEWLINE") in 
  let val wildcard__429_500_1574_2229 = (print "Running pass barnesHutPotential (fold_like, uses=11): ") in 
  let val wildcard__427_501_1575_2230 = (print "NEWLINE") in 
  let val bhPotential_502_1576_2231 = (barnesHutPotential(octTree_479_1553_2208 , 21, 60)) in 
  let val wildcard__423_503_1577_2232 = (print "End") in 
  let val wildcard__421_504_1578_2233 = (print "NEWLINE") in 
  let val wildcard__419_505_1579_2234 = (print "Running pass fmmPotential (fold_like, uses=12): ") in 
  let val wildcard__417_506_1580_2235 = (print "NEWLINE") in 
  let val fmmPot_507_1581_2236 = (fmmPotential(octTree_479_1553_2208 , 21, 4, 70)) in 
  let val wildcard__413_508_1582_2237 = (print "End") in 
  let val wildcard__411_509_1583_2238 = (print "NEWLINE") in 
  let val wildcard__409_510_1584_2239 = (print "Running pass scaleEnergy (map, uses=16): ") in 
  let val wildcard__407_511_1585_2240 = (print "NEWLINE") in 
  let val octTree__512_1586_2241 = (scaleEnergy(octTree_479_1553_2208 , 9)) in 
  let val wildcard__403_513_1587_2242 = (print "End") in 
  let val wildcard__401_514_1588_2243 = (print "NEWLINE") in 
  let val wildcard__399_515_1589_2244 = (print "Running pass clearFlags (map, uses=15): ") in 
  let val wildcard__397_516_1590_2245 = (print "NEWLINE") in 
  let val octTree___517_1591_2246 = (clearFlags octTree_479_1553_2208) in 
  let val wildcard__393_518_1592_2247 = (print "End") in 
  let val wildcard__391_519_1593_2248 = (print "NEWLINE") in 
  let val scaledEnergy_520_1594_2249 = (sumEnergy octTree__512_1586_2241) in 
  let val clearedActive_521_1595_2250 = (countActive(octTree___517_1591_2246 , 60)) in (totMass_482_1556_2211 , totEnergy_487_1561_2216, totActive_492_1566_2221, totParticles_497_1571_2226, bhPotential_502_1576_2231, fmmPot_507_1581_2236, scaledEnergy_520_1594_2249, clearedActive_521_1595_2250) end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end end of (x__1 , x__2, x__3, x__4, x__5, x__6, x__7, x__8) -> let val _ = print "#(" val _ = (print(Int.toString(x__1))) val _ = print " "val _ = (print(Int.toString(x__2))) val _ = print " "val _ = (print(Int.toString(x__3))) val _ = print " "val _ = (print(Int.toString(x__4))) val _ = print " "val _ = (print(Int.toString(x__5))) val _ = print " "val _ = (print(Int.toString(x__6))) val _ = print " "val _ = (print(Int.toString(x__7))) val _ = print " "val _ = (print(Int.toString(x__8))) val _ = print " " val _ = print ")" in ());
val _ = print "\n"
