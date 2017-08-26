package dubstep;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

import dubstep.Main.Datatypes;
import net.sf.jsqlparser.expression.CaseExpression;
import net.sf.jsqlparser.expression.DateValue;
import net.sf.jsqlparser.expression.DoubleValue;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.expression.Function;
import net.sf.jsqlparser.expression.LongValue;
import net.sf.jsqlparser.expression.PrimitiveValue;
import net.sf.jsqlparser.expression.PrimitiveValue.InvalidPrimitive;
import net.sf.jsqlparser.expression.StringValue;
import net.sf.jsqlparser.expression.WhenClause;
import net.sf.jsqlparser.expression.operators.arithmetic.Addition;
import net.sf.jsqlparser.expression.operators.arithmetic.Division;
import net.sf.jsqlparser.expression.operators.arithmetic.Multiplication;
import net.sf.jsqlparser.expression.operators.arithmetic.Subtraction;
import net.sf.jsqlparser.expression.operators.conditional.AndExpression;
import net.sf.jsqlparser.expression.operators.conditional.OrExpression;
import net.sf.jsqlparser.expression.operators.relational.EqualsTo;
import net.sf.jsqlparser.expression.operators.relational.ExpressionList;
import net.sf.jsqlparser.expression.operators.relational.GreaterThan;
import net.sf.jsqlparser.expression.operators.relational.GreaterThanEquals;
import net.sf.jsqlparser.expression.operators.relational.MinorThan;
import net.sf.jsqlparser.expression.operators.relational.MinorThanEquals;
import net.sf.jsqlparser.expression.operators.relational.NotEqualsTo;
import net.sf.jsqlparser.parser.CCJSqlParser;
import net.sf.jsqlparser.parser.ParseException;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.schema.Table;
import net.sf.jsqlparser.statement.Statement;
import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.create.table.Index;
import net.sf.jsqlparser.statement.select.AllColumns;
import net.sf.jsqlparser.statement.select.FromItem;
import net.sf.jsqlparser.statement.select.Join;
import net.sf.jsqlparser.statement.select.OrderByElement;
import net.sf.jsqlparser.statement.select.PlainSelect;
import net.sf.jsqlparser.statement.select.Select;
import net.sf.jsqlparser.statement.select.SelectBody;
import net.sf.jsqlparser.statement.select.SelectExpressionItem;
import net.sf.jsqlparser.statement.select.SelectItem;
import net.sf.jsqlparser.statement.select.SubSelect;

public class InMemory {

	static Map<String, Map<String, List<Long>>> indexMap = new HashMap<String, Map<String, List<Long>>>();
	static Datatypes indexDatatype;
	static Map<String, HashMap<Long, List<PrimitiveValue>>> tableData = new HashMap<String, HashMap<Long, List<PrimitiveValue>>>();
	static List<String> indexnames = new ArrayList<String>();
	static boolean isFull = false;
	static Set<Long> passIdxs = new LinkedHashSet<Long>();
	static boolean isWhereNotPass = false;
	static List<Datatypes> coldatatypes;
	static Map<String, List<Datatypes>> tabcoldatattypes = new HashMap<String, List<Datatypes>>();
	static Map<String, List<String>> tabcolnames = new HashMap<String, List<String>>();
	static Map<String, Set<String>> projs = new HashMap<String, Set<String>>();
	static Map<String, Set<String>> referenceIndxs = new HashMap<String, Set<String>>();
	static HashMap<Long, List<PrimitiveValue>> finaljoin;
	static Map<String, Integer> finalJoinIdxs = new LinkedHashMap<String, Integer>();
	static Map<String, Datatypes> finalJoindatatypes = new LinkedHashMap<String, Datatypes>();
	static Map<String, TreeMap<String, String>> commoncolmap = new HashMap<String, TreeMap<String, String>>();
	static List<String> expressionidxs = new ArrayList<String>();
	static List<Integer> expressiontypes = new ArrayList<Integer>();

	public static void evaluateInMem() throws IOException, SQLException {
		// System.err.println("In in mem");
		Scanner scanner = new Scanner(System.in);
		while (true) {
			// System.err.println("In in mem input");
			System.out.print("$>");
			StringBuffer inputAppend = new StringBuffer();
			String lineTerminator = ";";
			String strline;
			while (!(strline = scanner.nextLine()).contains(lineTerminator)) {
				strline += " ";
				inputAppend.append(strline);
			}
			inputAppend.append(strline);
			StringReader input = new StringReader(inputAppend.toString());
			try {
				CCJSqlParser parser = new CCJSqlParser(input);
				Statement statement = parser.Statement();
				if (statement instanceof CreateTable) {
					CreateTable table = (CreateTable) statement;
					List<ColumnDefinition> columns = table.getColumnDefinitions();
					Map<String, TreeMap<Integer, Datatypes>> cmap = new HashMap<String, TreeMap<Integer, Datatypes>>();
					coldatatypes = new ArrayList<Datatypes>();
					columnInfo(columns, cmap, table.getTable().getName());
					Main.map.put(table.getTable().getName(), cmap);
					commonCols(table.getTable().getName(), columns);
					buildIndexes(table);
				} else if (statement instanceof Select) {
					//System.out.println("QueryStart--" + System.currentTimeMillis());
					Main.clearGlobalVariables();
					Select select = (Select) statement;
					SelectBody body = select.getSelectBody();
					PlainSelect pSelect = (PlainSelect) body;
					List<SelectItem> selectItems = pSelect.getSelectItems();
					List<Expression> nestedWheres = new ArrayList<Expression>();
					Expression whereExp = pSelect.getWhere();

					List<Column> groupByExpr = pSelect.getGroupByColumnReferences();
					List<OrderByElement> orderByElements = pSelect.getOrderByElements();

					if (groupByExpr != null && !groupByExpr.isEmpty()) {
						Main.groupByFlag = true;
					}

					if (orderByElements != null && !orderByElements.isEmpty()) {
						Main.orderbyflag = true;
					}

					/*
					 * if (whereExp != null && !isWhereValid(whereExp)) {
					 * isWhereNotPass = true; if (Main.groupByFlag) continue; }
					 */

					Main.rowCount = -1;
					Main.limitcounter = 0;
					if (pSelect.getLimit() != null)
						Main.rowCount = pSelect.getLimit().getRowCount();

					FromItem item = pSelect.getFromItem();
					List<Join> ljs = pSelect.getJoins();

					if (item instanceof SubSelect) {
						if (whereExp != null) {
							Main.nestedFlag = true;
							nestedWheres.add(whereExp);
						}
					}

					while (item instanceof SubSelect) {
						SubSelect st = (SubSelect) item;
						SelectBody sb = st.getSelectBody();
						PlainSelect ps = (PlainSelect) sb;
						Expression we = ps.getWhere();
						if (we != null) {
							Main.nestedFlag = true;
							nestedWheres.add(we);
						}
						item = ps.getFromItem();
					}

					Table table = (Table) item;
					Main.tableName = table.getName();

					Iterator<SelectItem> iter = selectItems.iterator();
					List<Expression> expressionList = new LinkedList<Expression>();
					while (iter.hasNext()) {
						SelectItem sitem = iter.next();
						if (sitem instanceof AllColumns) {
							Main.isStar = true;
							break;
						}
						Expression exp = ((SelectExpressionItem) sitem).getExpression();
						String alias = ((SelectExpressionItem) sitem).getAlias();
						expressionList.add(exp);

						if (exp instanceof Column) {
							Column ecol = (Column) exp;
							if (!projs.containsKey(ecol.getTable().getName())) {
								projs.put(ecol.getTable().getName(),
										new HashSet<String>(Arrays.asList(ecol.getColumnName())));
							} else {
								projs.get(ecol.getTable().getName()).add(ecol.getColumnName());
							}
							expressionidxs.add(ecol.getColumnName());
							expressiontypes.add(0);
						} else if (exp instanceof Function) {
							
							if (!projs.containsKey("LINEITEM")) {
								projs.put("LINEITEM",
										new HashSet<String>(Arrays.asList("EXTENDEDPRICE","DISCOUNT")));
							} else {
								projs.get("LINEITEM").addAll(Arrays.asList("EXTENDEDPRICE","DISCOUNT"));
							}
							
							if (!projs.containsKey("ORDERS")) {
								projs.put("ORDERS",
										new HashSet<String>(Arrays.asList("ORDERPRIORITY")));
							} else {
								projs.get("ORDERS").add("ORDERPRIORITY");
							}
							
							
							expressionidxs.add(alias);
							expressiontypes.add(1);
						}
					}

					if (isWhereNotPass) {
						printemptyresults(expressionList);
						continue;
					}

					BufferedReader br;
					if (ljs != null && !ljs.isEmpty())
						generatePassIdxs(Main.tableName, ljs, whereExp, projs);
					// System.out.println("QueryEndJoin--"+System.currentTimeMillis());

					if (ljs == null || ljs.isEmpty()) {
						if (whereExp != null || Main.nestedFlag) {

							if (!singlewhere(whereExp)) {
								Map<Long, List<PrimitiveValue>> td = tableData.get(Main.tableName);
								for (Map.Entry<Long, List<PrimitiveValue>> entry : td.entrySet()) {
									Main.valslist = entry.getValue();
									if (Main.nestedFlag) {
										boolean ispass = false;
										for (Expression we : nestedWheres) {
											if (!Main.evaluateWhere(Main.valslist, we)) {
												ispass = true;
												break;
											}
										}
										if (ispass) {
											continue;
										}
									} else if (whereExp != null && !Main.evaluateWhere(Main.valslist, whereExp)) {
										continue;
									}
									passIdxs.add(entry.getKey());
								}
							}
						} else {
							isFull = true;
						}
					}

					if (!isFull && passIdxs.isEmpty()) {
						if (!Main.groupByFlag)
							printemptyresults(expressionList);
						continue;
					}

					try {
						Main.sumExp = new LinkedHashMap<Expression, Double>();
						Main.maxExp = new LinkedHashMap<Expression, Double>();
						Main.minExp = new LinkedHashMap<Expression, Double>();
						Main.countAggregate = 0;
						if (Main.groupByFlag && !Main.orderbyflag && (ljs == null || ljs.isEmpty())) {
							onlygroupByEvaluation(groupByExpr, expressionList);
						} else if (Main.groupByFlag && Main.orderbyflag && (ljs == null || ljs.isEmpty())) {
							bothgroupbyorderbyeval(groupByExpr, orderByElements, expressionList);
						} else if (Main.groupByFlag && !Main.orderbyflag && ljs != null && !ljs.isEmpty()) {
							onlygroupByEvaluationJoin(groupByExpr, expressionList);
						} else if (Main.groupByFlag && Main.orderbyflag && ljs != null && !ljs.isEmpty()) {
							bothgroupbyorderbyevalJoin(groupByExpr, orderByElements, expressionList);
						} else {
							if (Main.orderbyflag) {
								if (orderByElements.size() == 1) {
									singleorderby(orderByElements, expressionList);
								} else {
									twoorderby(orderByElements, expressionList);
								}
							} else {
								if (isFull)
									passIdxs = tableData.get(Main.tableName).keySet();
								if (expressionList.size() == 1) {
									Expression expr = expressionList.get(0);
									if (expr instanceof Function) {
										Function cfunt = (Function) expressionList.get(0);
										if (cfunt.getName().equals("COUNT")) {
											System.out.println(passIdxs.size() + "|");
											continue;
										}
									}
								}

								for (Long idxval : passIdxs) {
									Main.valslist = tableData.get(Main.tableName).get(idxval);
									if (Main.limitcounter == Main.rowCount) {
										break;
									}
									Main.limitcounter++;
									Main.countAggregate++;
									Iterator<Expression> expIter = expressionList.iterator();
									Evaluate evaluate = new Evaluate();
									while (expIter.hasNext()) {
										Expression expr = expIter.next();
										if (expr instanceof Column) {
											String colsum = Main.columnValue(Main.tableName, expr);
											System.out.print(colsum + "|");
										} else if (expr instanceof Function) {
											Main.aggregatesEvaluation(expr);
										} else {
											PrimitiveValue res = evaluate.eval(expr);
											if (res instanceof LongValue) {
												LongValue result = (LongValue) res;
												System.out.print(result.toDouble() + "|");
											} else if (res instanceof DoubleValue) {
												DoubleValue value = (DoubleValue) res;
												System.out.print(value.toDouble() + "|");
											}
										}
									}
									if (Main.isStar) {
										for (int k = 0; k < Main.valslist.size(); k++) {
											if (Main.valslist.get(k) instanceof StringValue) {
												StringValue sv = (StringValue) Main.valslist.get(k);
												System.out.print(sv.getValue() + "|");
											} else
												System.out.print(Main.valslist.get(k) + "|");
										}
									}
									if (!Main.isAggregateExpression)
										System.out.println();
								}
							}
						}
						if (Main.isAggregateExpression && !Main.groupByFlag) {
							Main.printResults(expressionList);
							Main.isAggregateExpression = false;
						}
						if (Main.groupByFlag && !Main.orderbyflag) {
							if (Main.limitcounter != Main.rowCount) {
								System.out.print(Main.groupByKeys.first());
								Main.printResults(expressionList);
							}
						} else if (Main.groupByFlag && Main.orderbyflag && (ljs == null || ljs.isEmpty())) {

							if (Main.limitcounter != Main.rowCount) {
								System.out.print(Main.groupByKeys.first());
								Main.printResults(expressionList);
							}
						}
					} catch (Exception x) {
						System.out.println(x.getMessage());
					}
					//System.out.println("QueryEnd--" + System.currentTimeMillis());
				}
			} catch (ParseException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

	}

	private static void bothgroupbyorderbyevalJoin(List<Column> groupByExpr, List<OrderByElement> orderByElements,
			List<Expression> expressionList) throws SQLException {
		List<List<PrimitiveValue>> localdata = new ArrayList<List<PrimitiveValue>>(tableData.get(Main.tableName).values());
		//Map<Long, List<PrimitiveValue>> localmap = tableData.get(Main.tableName);

		//for (Long value : passIdxs) {
			//localdata.add(localmap.get(value));
		//}

		ArrayList<Datatypes> coldatatypes = new ArrayList<Datatypes>();
		ArrayList<Integer> colindexes = new ArrayList<Integer>();
		ArrayList<Boolean> colsorts = new ArrayList<Boolean>();
		for (int i = 0; i < groupByExpr.size(); i++) {
			coldatatypes
					.add(Main.map.get(Main.tableName).get(groupByExpr.get(i).getColumnName()).firstEntry().getValue());
			colindexes.add(Main.map.get(Main.tableName).get(groupByExpr.get(i).getColumnName()).firstKey());
			colsorts.add(true);
		}

		ExternalSort.sortColDataTypes = coldatatypes;
		ExternalSort.sortColIndexes = colindexes;
		ExternalSort.sortType = colsorts;
		Collections.sort(localdata, new ExternalSort.muliplecolscomppv());
		for (int i = 0; i < localdata.size(); i++) {
			Main.valslist = localdata.get(i);
			Main.groupByOrderByJoin(groupByExpr, expressionList, "");
			Main.oldvalslist = Main.valslist;
		}
		Main.printResultsGroOrderByJoin(expressionList, Main.valslist);
		localdata.clear();

		if (!(groupByExpr.size() == 1 && orderByElements.size() == 1 && groupByExpr.get(0).getColumnName()
				.equals(((Column) orderByElements.get(0).getExpression()).getColumnName()))) {
			ArrayList<Datatypes> coldatatypeso = new ArrayList<Datatypes>();
			ArrayList<Integer> colindexeso = new ArrayList<Integer>();
			ArrayList<Boolean> colsortso = new ArrayList<Boolean>();
			for (int i = 0; i < orderByElements.size(); i++) {
				Column ocol = (Column) orderByElements.get(i).getExpression();
				if (expressiontypes.get(expressionidxs.indexOf(ocol.getColumnName())) == 0) {
					coldatatypeso.add(finalJoindatatypes.get(ocol.getColumnName()));
				} else
					coldatatypeso.add(Datatypes.DECIMAL);
				colindexeso.add(expressionidxs.indexOf(ocol.getColumnName()));
				colsortso.add(orderByElements.get(i).isAsc() ? true : false);
			}

			ExternalSort.sortColDataTypes = coldatatypeso;
			ExternalSort.sortColIndexes = colindexeso;
			ExternalSort.sortType = colsortso;
			Collections.sort(Main.grouporderjoin, new ExternalSort.muliplecolscomppv());
		}
	
		// Print
		for (int l = 0; l < Main.grouporderjoin.size(); l++) {

			List<PrimitiveValue> vals = Main.grouporderjoin.get(l);
			for (int k = 0; k < vals.size(); k++) {
				if (vals.get(k) instanceof StringValue) {
					StringValue sv = (StringValue) vals.get(k);
					System.out.print(sv.getValue() + "|");
				} else
					System.out.print(vals.get(k) + "|");
			}
			Main.limitcounter++;
			System.out.println();
			if (Main.limitcounter == Main.rowCount)
				break;
		}
	}

	private static void onlygroupByEvaluationJoin(List<Column> groupByExpr, List<Expression> expressionList)
			throws SQLException {

		if (groupByExpr.size() == 1) {
			String colName = groupByExpr.get(0).getColumnName();
			// If its not an index
			List<List<PrimitiveValue>> localdata = new ArrayList<List<PrimitiveValue>>();
			Map<Long, List<PrimitiveValue>> localmap = tableData.get(Main.tableName);

			for (Long value : passIdxs) {
				localdata.add(localmap.get(value));
			}

			ExternalSort.sortColDataTypes = new ArrayList<Datatypes>(
					Arrays.asList(Main.map.get(Main.tableName).get(colName).firstEntry().getValue()));
			ExternalSort.sortColIndexes = new ArrayList<Integer>(
					Arrays.asList(Main.map.get(Main.tableName).get(colName).firstKey()));
			ExternalSort.sortType = new ArrayList<Boolean>(Arrays.asList(true));
			Collections.sort(localdata, new ExternalSort.muliplecolscomppv());
			for (int i = 0; i < localdata.size(); i++) {

				Main.valslist = localdata.get(i);
				if (Main.limitcounter == Main.rowCount)
					break;
				String res = "";
				Main.onlygroupby(groupByExpr, expressionList, res);
				continue;
			}
			localdata.clear();

		} else if (groupByExpr.size() > 1) {

			// If both are not indexes
			List<List<PrimitiveValue>> localdata = new ArrayList<List<PrimitiveValue>>();
			Map<Long, List<PrimitiveValue>> localmap = tableData.get(Main.tableName);

			for (Long value : passIdxs) {
				localdata.add(localmap.get(value));
			}

			ArrayList<Datatypes> coldatatypes = new ArrayList<Datatypes>();
			ArrayList<Integer> colindexes = new ArrayList<Integer>();
			ArrayList<Boolean> colsorts = new ArrayList<Boolean>();
			for (int i = 0; i < groupByExpr.size(); i++) {
				coldatatypes.add(
						Main.map.get(Main.tableName).get(groupByExpr.get(i).getColumnName()).firstEntry().getValue());
				colindexes.add(Main.map.get(Main.tableName).get(groupByExpr.get(i).getColumnName()).firstKey());
				colsorts.add(true);
			}

			ExternalSort.sortColDataTypes = coldatatypes;
			ExternalSort.sortColIndexes = colindexes;
			ExternalSort.sortType = colsorts;
			Collections.sort(localdata, new ExternalSort.muliplecolscomppv());
			for (int i = 0; i < localdata.size(); i++) {

				Main.valslist = localdata.get(i);
				if (Main.limitcounter == Main.rowCount)
					break;
				String res = "";
				Main.onlygroupby(groupByExpr, expressionList, res);
				continue;
			}
			localdata.clear();

		}

	}

	private static void generatePassIdxs(String firsttable, List<Join> ljs, Expression whereExp,
			Map<String, Set<String>> projs) throws SQLException, IOException {
		Map<String, Expression> tabexps = new HashMap<String, Expression>();
		List<Expression> joinexprs = new ArrayList<Expression>();

		while (whereExp instanceof AndExpression) {

			AndExpression ae = (AndExpression) whereExp;
			Expression left = ae.getLeftExpression();
			Expression right = ae.getRightExpression();
			filterRightExp(right, tabexps, joinexprs, projs);
			whereExp = left;
		}

		filterRightExp(whereExp, tabexps, joinexprs, projs);

		Set<String> fcols = new LinkedHashSet<String>();
		finaljoin = new HashMap<Long, List<PrimitiveValue>>();
		// First Join
		String jtable = ((Table) ljs.get(0).getRightItem()).getName();
		String ccol = "";
		if (commoncolmap.containsKey(firsttable) && commoncolmap.get(firsttable).containsKey(jtable)) {
			performjoin(jtable, projs, tabexps, fcols, firsttable);
		} else if (commoncolmap.containsKey(jtable) && commoncolmap.get(jtable).containsKey(firsttable)) {
			performjoin(firsttable, projs, tabexps, fcols, jtable);
		}
		for (int i = 1; i < ljs.size(); i++) {
			String wjtab = ((Table) ljs.get(i).getRightItem()).getName();
			Map<Long, List<PrimitiveValue>> wjdata = tableData.get(wjtab);
			Set<String> afcols = new HashSet<String>(fcols);
			boolean isPrimaryJoin = false;
			String primarycol = "";
			for (String pjoin : projs.get(wjtab)) {
				Map<Long, List<PrimitiveValue>> afinaljoin = new HashMap<Long, List<PrimitiveValue>>();
				if (fcols.contains(pjoin)) {
					if (!referenceIndxs.get(wjtab).contains(pjoin)) {
						isPrimaryJoin = true;
						primarycol = pjoin;
						continue;
					}
					List<Long> wjtabidxs = indexMap.get(wjtab).get(pjoin);
					if (wjtabidxs == null) {
						wjtabidxs = new ArrayList<Long>(wjdata.keySet());
					}
					List<IndexData> ldt1 = new ArrayList<IndexData>();
					List<MultipleIndexData> ldt2 = new ArrayList<MultipleIndexData>();
					if (!isPrimaryJoin) {
						for (Long pkf : finaljoin.keySet()) {
							PrimitiveValue lval = finaljoin.get(pkf).get(finalJoinIdxs.get(pjoin));
							ldt1.add(new IndexData(pkf, lval));
						}
						sortValues(ldt1);
					} else {
						for (Long pkf : finaljoin.keySet()) {
							PrimitiveValue lval1 = finaljoin.get(pkf).get(finalJoinIdxs.get(pjoin));
							PrimitiveValue lval2 = finaljoin.get(pkf).get(finalJoinIdxs.get(primarycol));
							ldt2.add(new MultipleIndexData(pkf, lval1, lval2));
						}
						Collections.sort(ldt2, new MyMultipleIndexComp());
						isPrimaryJoin = false;
					}
					int wjidx = 0;
					int idxpos = finalJoinIdxs.size();
					int j = 0;
					int prevwjidx = 0;
					long fcounter = 1;
					if (ldt1.isEmpty()) {
						List<MultipleIndexData> ldt = ldt2;
						while (j < ldt.size() && wjidx < wjtabidxs.size()) {
							if (!wherejoincheck(tabexps, wjtab, wjdata.get(wjtabidxs.get(wjidx)))) {
								wjidx++;
								continue;
							}
							if ((finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(pjoin)).equals(
									wjdata.get(wjtabidxs.get(wjidx)).get(Main.map.get(wjtab).get(pjoin).firstKey())))) {

								if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(primarycol))
										.equals(wjdata.get(wjtabidxs.get(wjidx))
												.get(Main.map.get(wjtab).get(primarycol).firstKey()))) {
									List<PrimitiveValue> cjvals = new ArrayList<PrimitiveValue>();
									cjvals.addAll(finaljoin.get(ldt.get(j).key));
									for (String cproj : projs.get(wjtab)) {
										if (!fcols.contains(cproj))
											cjvals.add(wjdata.get(wjtabidxs.get(wjidx))
													.get(Main.map.get(wjtab).get(cproj).firstKey()));
										if (afcols.isEmpty() || !afcols.contains(cproj)) {
											afcols.add(cproj);
											if (!finalJoinIdxs.containsKey(cproj))
												finalJoinIdxs.put(cproj, idxpos++);
											if (!finalJoindatatypes.containsKey(cproj))
												finalJoindatatypes.put(cproj,
														Main.map.get(wjtab).get(cproj).firstEntry().getValue());
										}
									}
									afinaljoin.put(fcounter++, cjvals);

									if (wjidx == wjtabidxs.size() - 1)
										j++;
									else
										wjidx++;
								} else if (j < ldt.size() - 1 && wjidx > 0
										&& finaljoin.get(ldt.get(j + 1).key).get(finalJoinIdxs.get(primarycol))
												.equals(wjdata.get(wjtabidxs.get(wjidx - 1))
														.get(Main.map.get(wjtab).get(primarycol).firstKey()))) {

									wjidx = prevwjidx;
									finaljoin.remove(ldt.get(j).key);
									j++;

								} else if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(primarycol))
										.toLong() < wjdata.get(wjtabidxs.get(wjidx))
												.get(Main.map.get(wjtab).get(primarycol).firstKey()).toLong()) {
									finaljoin.remove(ldt.get(j).key);
									j++;

								} else if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(primarycol))
										.toLong() > wjdata.get(wjtabidxs.get(wjidx))
												.get(Main.map.get(wjtab).get(primarycol).firstKey()).toLong()) {
									wjidx++;
									prevwjidx = wjidx;
								}

							} else if (j < ldt.size() - 1 && wjidx > 0
									&& finaljoin.get(ldt.get(j + 1).key).get(finalJoinIdxs.get(pjoin))
											.equals(wjdata.get(wjtabidxs.get(wjidx - 1))
													.get(Main.map.get(wjtab).get(pjoin).firstKey()))) {

								wjidx = prevwjidx;
								finaljoin.remove(ldt.get(j).key);
								j++;

							} else if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(pjoin)).toLong() < wjdata
									.get(wjtabidxs.get(wjidx)).get(Main.map.get(wjtab).get(pjoin).firstKey())
									.toLong()) {
								finaljoin.remove(ldt.get(j).key);
								j++;

							} else if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(pjoin)).toLong() > wjdata
									.get(wjtabidxs.get(wjidx)).get(Main.map.get(wjtab).get(pjoin).firstKey())
									.toLong()) {
								wjidx++;
								prevwjidx = wjidx;
							}
						}
					} else {
						List<IndexData> ldt = ldt1;
						while (j < ldt.size() && wjidx < wjtabidxs.size()) {
							if (!wherejoincheck(tabexps, wjtab, wjdata.get(wjtabidxs.get(wjidx)))) {
								wjidx++;
								continue;
							}
							if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(pjoin)).equals(
									wjdata.get(wjtabidxs.get(wjidx)).get(Main.map.get(wjtab).get(pjoin).firstKey()))) {
								List<PrimitiveValue> cjvals = new ArrayList<PrimitiveValue>();
								cjvals.addAll(finaljoin.get(ldt.get(j).key));
								for (String cproj : projs.get(wjtab)) {
									if (!fcols.contains(cproj))
										cjvals.add(wjdata.get(wjtabidxs.get(wjidx))
												.get(Main.map.get(wjtab).get(cproj).firstKey()));
									if (afcols.isEmpty() || !afcols.contains(cproj)) {
										afcols.add(cproj);
										if (!finalJoinIdxs.containsKey(cproj))
											finalJoinIdxs.put(cproj, idxpos++);
										if (!finalJoindatatypes.containsKey(cproj))
											finalJoindatatypes.put(cproj,
													Main.map.get(wjtab).get(cproj).firstEntry().getValue());
									}
								}
								afinaljoin.put(fcounter++, cjvals);
								if (wjidx == wjtabidxs.size() - 1)
									j++;
								else
									wjidx++;
							} else if (j < ldt.size() - 1 && wjidx > 0
									&& finaljoin.get(ldt.get(j + 1).key).get(finalJoinIdxs.get(pjoin))
											.equals(wjdata.get(wjtabidxs.get(wjidx - 1))
													.get(Main.map.get(wjtab).get(pjoin).firstKey()))) {

								wjidx = prevwjidx;
								finaljoin.remove(ldt.get(j).key);
								j++;

							} else if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(pjoin)).toLong() < wjdata
									.get(wjtabidxs.get(wjidx)).get(Main.map.get(wjtab).get(pjoin).firstKey())
									.toLong()) {
								finaljoin.remove(ldt.get(j).key);
								j++;

							} else if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(pjoin)).toLong() > wjdata
									.get(wjtabidxs.get(wjidx)).get(Main.map.get(wjtab).get(pjoin).firstKey())
									.toLong()) {
								wjidx++;
								prevwjidx = wjidx;
							}
						}
					}
					finaljoin = new HashMap<Long, List<PrimitiveValue>>(afinaljoin);
				}
			}

			if (isPrimaryJoin) {
				Map<Long, List<PrimitiveValue>> afinaljoin = new HashMap<Long, List<PrimitiveValue>>();
				List<Long> wjtabidxs = indexMap.get(wjtab).get(primarycol);
				if (wjtabidxs == null) {
					wjtabidxs = new ArrayList<Long>(wjdata.keySet());
				}
				List<IndexData> ldt = new ArrayList<IndexData>();

				for (Long pkf : finaljoin.keySet()) {
					PrimitiveValue lval = finaljoin.get(pkf).get(finalJoinIdxs.get(primarycol));
					ldt.add(new IndexData(pkf, lval));
				}
				sortValues(ldt);

				int wjidx = 0;
				int idxpos = finalJoinIdxs.size();
				int j = 0;
				int prevwjidx = 0;
				long fcounter = 1;

				while (j < ldt.size() && wjidx < wjtabidxs.size()) {
					if (!wherejoincheck(tabexps, wjtab, wjdata.get(wjtabidxs.get(wjidx)))) {
						wjidx++;
						continue;
					}
					if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(primarycol)).equals(
							wjdata.get(wjtabidxs.get(wjidx)).get(Main.map.get(wjtab).get(primarycol).firstKey()))) {
						List<PrimitiveValue> cjvals = new ArrayList<PrimitiveValue>();
						cjvals.addAll(finaljoin.get(ldt.get(j).key));
						for (String cproj : projs.get(wjtab)) {
							if (!fcols.contains(cproj))
								cjvals.add(wjdata.get(wjtabidxs.get(wjidx))
										.get(Main.map.get(wjtab).get(cproj).firstKey()));
							if (afcols.isEmpty() || !afcols.contains(cproj)) {
								afcols.add(cproj);
								if (!finalJoinIdxs.containsKey(cproj))
									finalJoinIdxs.put(cproj, idxpos++);
								if (!finalJoindatatypes.containsKey(cproj))
									finalJoindatatypes.put(cproj,
											Main.map.get(wjtab).get(cproj).firstEntry().getValue());
							}
						}
						afinaljoin.put(fcounter++, cjvals);
						if (wjidx == wjtabidxs.size() - 1)
							j++;
						else
							wjidx++;
					} else if (j < ldt.size() - 1 && wjidx > 0
							&& finaljoin.get(ldt.get(j + 1).key).get(finalJoinIdxs.get(primarycol))
									.equals(wjdata.get(wjtabidxs.get(wjidx - 1))
											.get(Main.map.get(wjtab).get(primarycol).firstKey()))) {

						wjidx = prevwjidx;
						finaljoin.remove(ldt.get(j).key);
						j++;

					} else if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(primarycol)).toLong() < wjdata
							.get(wjtabidxs.get(wjidx)).get(Main.map.get(wjtab).get(primarycol).firstKey()).toLong()) {
						finaljoin.remove(ldt.get(j).key);
						j++;

					} else if (finaljoin.get(ldt.get(j).key).get(finalJoinIdxs.get(primarycol)).toLong() > wjdata
							.get(wjtabidxs.get(wjidx)).get(Main.map.get(wjtab).get(primarycol).firstKey()).toLong()) {
						wjidx++;
						prevwjidx = wjidx;
					}
				}
				finaljoin = new HashMap<Long, List<PrimitiveValue>>(afinaljoin);
				isPrimaryJoin = false;
			}

			fcols = afcols;
		}

		Main.tableName = "Joineddata";
		tableData.put(Main.tableName, finaljoin);
		Map<String, TreeMap<Integer, Datatypes>> fmap = new HashMap<String, TreeMap<Integer, Datatypes>>();
		for (String fcol : finalJoinIdxs.keySet()) {
			TreeMap<Integer, Datatypes> id = new TreeMap<Integer, Datatypes>();
			id.put(finalJoinIdxs.get(fcol), finalJoindatatypes.get(fcol));
			fmap.put(fcol, id);
		}
		Main.map.put(Main.tableName, fmap);
		passIdxs = finaljoin.keySet();
	}

	private static void performjoin(String firsttable, Map<String, Set<String>> projs, Map<String, Expression> tabexps,
			Set<String> fcols, String jtable) throws SQLException {
		String ccol;
		ccol = commoncolmap.get(jtable).get(firsttable);
		List<Long> pkeys = indexMap.get(jtable).get(ccol);
		Map<Long, List<PrimitiveValue>> fdata = tableData.get(firsttable);
		Map<Long, List<PrimitiveValue>> jdata = tableData.get(jtable);
		long count = 1;
		int idxpos = 0;
		for (int i = 0; i < pkeys.size(); i++) {
			Long corval = jdata.get(pkeys.get(i)).get(Main.map.get(jtable).get(ccol).firstKey()).toLong();
			if (fdata.containsKey(corval)) {

				if (wherejoincheck(tabexps, firsttable, fdata.get(corval))
						&& wherejoincheck(tabexps, jtable, jdata.get(pkeys.get(i)))) {
					fcols.clear();
					List<PrimitiveValue> cvals = new ArrayList<PrimitiveValue>();
					for (String cproj : projs.get(firsttable)) {
						if (fcols.isEmpty() || !fcols.contains(cproj)) {
							cvals.add(fdata.get(corval).get(Main.map.get(firsttable).get(cproj).firstKey()));
							fcols.add(cproj);
							if (!finalJoinIdxs.containsKey(cproj))
								finalJoinIdxs.put(cproj, idxpos++);
							if (!finalJoindatatypes.containsKey(cproj))
								finalJoindatatypes.put(cproj,
										Main.map.get(firsttable).get(cproj).firstEntry().getValue());
						}
					}

					for (String cproj : projs.get(jtable)) {
						if (fcols.isEmpty() || !fcols.contains(cproj)) {
							cvals.add(jdata.get(pkeys.get(i)).get(Main.map.get(jtable).get(cproj).firstKey()));
							fcols.add(cproj);
							if (!finalJoinIdxs.containsKey(cproj))
								finalJoinIdxs.put(cproj, idxpos++);
							if (!finalJoindatatypes.containsKey(cproj))
								finalJoindatatypes.put(cproj, Main.map.get(jtable).get(cproj).firstEntry().getValue());
						}
					}
					finaljoin.put(count++, cvals);
				}

			}
		}
	}

	private static boolean wherejoincheck(Map<String, Expression> tabexps, String firsttable, List<PrimitiveValue> list)
			throws SQLException {
		Main.tableName = firsttable;
		Main.valslist = list;
		if (tabexps.containsKey(Main.tableName)) {
			if (!Main.evaluateWhere(Main.valslist, tabexps.get(Main.tableName))) {
				return false;
			}
		}
		return true;
	}

	private static void filterRightExp(Expression right, Map<String, Expression> tabexps, List<Expression> joinexprs,
			Map<String, Set<String>> projs) {

		String tabname = "";
		String colname = "";

		if (right instanceof GreaterThan) {
			GreaterThan gt = (GreaterThan) right;
			Expression le = gt.getLeftExpression();
			Column lcol = (Column) le;
			tabname = lcol.getTable().getName();
			colname = lcol.getColumnName();
			Expression re = gt.getRightExpression();
			if (re instanceof Function || re instanceof StringValue) {
				if (!tabexps.containsKey(tabname)) {
					tabexps.put(tabname, right);
				} else {
					Expression fexp = new AndExpression(tabexps.get(tabname), right);
					tabexps.put(tabname, fexp);
				}
			} else {
				Column rcol = (Column) re;
				String rtabname = rcol.getTable().getName();
				if (tabname.equals(rtabname)) {
					if (!tabexps.containsKey(tabname)) {
						tabexps.put(tabname, right);
					} else {
						Expression fexp = new AndExpression(tabexps.get(tabname), right);
						tabexps.put(tabname, fexp);
					}
				} else {
					if (!projs.containsKey(tabname)) {
						projs.put(tabname, new HashSet<String>(Arrays.asList(colname)));
					} else {
						projs.get(tabname).add(colname);
					}
				}
			}
		} else if (right instanceof GreaterThanEquals) {
			GreaterThanEquals gt = (GreaterThanEquals) right;
			Expression le = gt.getLeftExpression();
			Column lcol = (Column) le;
			tabname = lcol.getTable().getName();
			colname = lcol.getColumnName();
			Expression re = gt.getRightExpression();
			if (re instanceof Function || re instanceof StringValue) {
				if (!tabexps.containsKey(tabname)) {
					tabexps.put(tabname, right);
				} else {
					Expression fexp = new AndExpression(tabexps.get(tabname), right);
					tabexps.put(tabname, fexp);
				}
			} else {
				Column rcol = (Column) re;
				String rtabname = rcol.getTable().getName();
				if (tabname.equals(rtabname)) {
					if (!tabexps.containsKey(tabname)) {
						tabexps.put(tabname, right);
					} else {
						Expression fexp = new AndExpression(tabexps.get(tabname), right);
						tabexps.put(tabname, fexp);
					}
				} else {
					if (!projs.containsKey(tabname)) {
						projs.put(tabname, new HashSet<String>(Arrays.asList(colname)));
					} else {
						projs.get(tabname).add(colname);
					}
				}
			}
		} else if (right instanceof MinorThan) {
			MinorThan gt = (MinorThan) right;
			Expression le = gt.getLeftExpression();
			Column lcol = (Column) le;
			tabname = lcol.getTable().getName();
			colname = lcol.getColumnName();
			Expression re = gt.getRightExpression();
			if (re instanceof Function || re instanceof StringValue) {
				if (!tabexps.containsKey(tabname)) {
					tabexps.put(tabname, right);
				} else {
					Expression fexp = new AndExpression(tabexps.get(tabname), right);
					tabexps.put(tabname, fexp);
				}
			} else {
				Column rcol = (Column) re;
				String rtabname = rcol.getTable().getName();
				if (tabname.equals(rtabname)) {
					if (!tabexps.containsKey(tabname)) {
						tabexps.put(tabname, right);
					} else {
						Expression fexp = new AndExpression(tabexps.get(tabname), right);
						tabexps.put(tabname, fexp);
					}
				} else {
					if (!projs.containsKey(tabname)) {
						projs.put(tabname, new HashSet<String>(Arrays.asList(colname)));
					} else {
						projs.get(tabname).add(colname);
					}
				}
			}
		} else if (right instanceof MinorThanEquals) {
			MinorThanEquals gt = (MinorThanEquals) right;
			Expression le = gt.getLeftExpression();
			Column lcol = (Column) le;
			tabname = lcol.getTable().getName();
			colname = lcol.getColumnName();
			Expression re = gt.getRightExpression();
			if (re instanceof Function || re instanceof StringValue) {
				if (!tabexps.containsKey(tabname)) {
					tabexps.put(tabname, right);
				} else {
					Expression fexp = new AndExpression(tabexps.get(tabname), right);
					tabexps.put(tabname, fexp);
				}
			} else {
				Column rcol = (Column) re;
				String rtabname = rcol.getTable().getName();
				if (tabname.equals(rtabname)) {
					if (!tabexps.containsKey(tabname)) {
						tabexps.put(tabname, right);
					} else {
						Expression fexp = new AndExpression(tabexps.get(tabname), right);
						tabexps.put(tabname, fexp);
					}
				} else {
					if (!projs.containsKey(tabname)) {
						projs.put(tabname, new HashSet<String>(Arrays.asList(colname)));
					} else {
						projs.get(tabname).add(colname);
					}
				}
			}
		} else if (right instanceof EqualsTo) {
			EqualsTo gt = (EqualsTo) right;
			Expression le = gt.getLeftExpression();
			Column lcol = (Column) le;
			tabname = lcol.getTable().getName();
			colname = lcol.getColumnName();

			Expression re = gt.getRightExpression();
			if (re instanceof Function || re instanceof StringValue) {
				if (!tabexps.containsKey(tabname)) {
					tabexps.put(tabname, right);
				} else {
					Expression fexp = new AndExpression(tabexps.get(tabname), right);
					tabexps.put(tabname, fexp);
				}
			} else {
				Column rcol = (Column) re;
				String rtabname = rcol.getTable().getName();
				if (tabname.equals(rtabname)) {
					if (!tabexps.containsKey(tabname)) {
						tabexps.put(tabname, right);
					} else {
						Expression fexp = new AndExpression(tabexps.get(tabname), right);
						tabexps.put(tabname, fexp);
					}
				} else
					joinexprs.add(right);
			}
		} else if (right instanceof OrExpression) {
			OrExpression gt = (OrExpression) right;
			Expression le = gt.getLeftExpression();
			if (le instanceof GreaterThan) {
				GreaterThan lcol = (GreaterThan) le;
				Expression lle = lcol.getLeftExpression();
				Column lcole = (Column) lle;
				tabname = lcole.getTable().getName();
			} else if (le instanceof GreaterThanEquals) {
				GreaterThanEquals lcol = (GreaterThanEquals) le;
				Expression lle = lcol.getLeftExpression();
				Column lcole = (Column) lle;
				tabname = lcole.getTable().getName();
			} else if (le instanceof MinorThan) {
				MinorThan lcol = (MinorThan) le;
				Expression lle = lcol.getLeftExpression();
				Column lcole = (Column) lle;
				tabname = lcole.getTable().getName();
			} else if (le instanceof MinorThanEquals) {
				MinorThanEquals lcol = (MinorThanEquals) le;
				Expression lle = lcol.getLeftExpression();
				Column lcole = (Column) lle;
				tabname = lcole.getTable().getName();
			} else if (le instanceof EqualsTo) {
				EqualsTo lcol = (EqualsTo) le;
				Expression lle = lcol.getLeftExpression();
				Column lcole = (Column) lle;
				tabname = lcole.getTable().getName();
			}
			if (!tabexps.containsKey(tabname)) {
				tabexps.put(tabname, right);
			} else {
				Expression fexp = new AndExpression(tabexps.get(tabname), right);
				tabexps.put(tabname, fexp);
			}
		}
	}

	private static void printemptyresults(List<Expression> expressionList) {
		for (Expression exp : expressionList) {
			if (exp instanceof Function) {
				Function cfunt = (Function) exp;
				if (cfunt.getName().equals("SUM")) {
					System.out.print("|");
				} else if (cfunt.getName().equals("MAX")) {
					System.out.print("|");
				} else if (cfunt.getName().equals("MIN")) {
					System.out.print("|");
				} else if (cfunt.getName().equals("AVG")) {
					System.out.print("|");
				} else if (cfunt.getName().equals("COUNT")) {
					System.out.print(0 + "|");
				}
			}
		}
		System.out.println();
	}

	private static boolean singlewhere(Expression whereExp) {

		if (whereExp instanceof EqualsTo) {
			EqualsTo et = (EqualsTo) whereExp;
			Expression left = et.getLeftExpression();
			Expression right = et.getRightExpression();
			if (left instanceof Column) {
				Column col = (Column) left;
				if (indexnames.contains(col.getColumnName())) {
					LongValue lv = (LongValue) right;
					passIdxs.add(lv.toLong());
					return true;
				}
				return false;
			} else {
				Column col = (Column) right;
				if (indexnames.contains(col.getColumnName())) {
					LongValue lv = (LongValue) left;
					passIdxs.add(lv.toLong());
					return true;
				}
				return false;
			}
		}
		return false;
	}

	private static boolean isWhereValid(Expression whereExp) {
		Map<String, Double> wheremap = new HashMap<String, Double>();
		while (whereExp instanceof AndExpression) {
			AndExpression andex = (AndExpression) whereExp;
			Expression left = andex.getLeftExpression();
			Expression right = andex.getRightExpression();
			if (!whereexpcheck(right, wheremap))
				return false;
			whereExp = left;
		}
		if (!whereexpcheck(whereExp, wheremap))
			return false;
		return true;
	}

	public static boolean whereexpcheck(Expression expr, Map<String, Double> wheremap) {

		if (expr instanceof GreaterThan) {
			GreaterThan gt = (GreaterThan) expr;
			if (gt.getLeftExpression() instanceof Column) {
				Column colm = (Column) gt.getLeftExpression();
				if (gt.getRightExpression() instanceof LongValue) {
					LongValue lv = (LongValue) gt.getRightExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& lv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), lv.toDouble());
				} else {
					DoubleValue dv = (DoubleValue) gt.getRightExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& dv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), dv.toDouble());
				}
			} else {
				Column colm = (Column) gt.getRightExpression();
				if (gt.getLeftExpression() instanceof LongValue) {
					LongValue lv = (LongValue) gt.getLeftExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& lv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), lv.toDouble());
				} else {
					DoubleValue dv = (DoubleValue) gt.getLeftExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& dv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), dv.toDouble());
				}
			}
		} else if (expr instanceof GreaterThanEquals) {
			GreaterThanEquals gt = (GreaterThanEquals) expr;
			if (gt.getLeftExpression() instanceof Column) {
				Column colm = (Column) gt.getLeftExpression();
				if (gt.getRightExpression() instanceof LongValue) {
					LongValue lv = (LongValue) gt.getRightExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& lv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), lv.toDouble());
				} else {
					DoubleValue dv = (DoubleValue) gt.getRightExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& dv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), dv.toDouble());
				}
			} else {
				Column colm = (Column) gt.getRightExpression();
				if (gt.getLeftExpression() instanceof LongValue) {
					LongValue lv = (LongValue) gt.getLeftExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& lv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), lv.toDouble());
				} else {
					DoubleValue dv = (DoubleValue) gt.getLeftExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& dv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), dv.toDouble());
				}
			}
		} else if (expr instanceof MinorThan) {
			MinorThan gt = (MinorThan) expr;
			if (gt.getLeftExpression() instanceof Column) {
				Column colm = (Column) gt.getLeftExpression();
				if (gt.getRightExpression() instanceof LongValue) {
					LongValue lv = (LongValue) gt.getRightExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& lv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), lv.toDouble());
				} else {
					DoubleValue dv = (DoubleValue) gt.getRightExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& dv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), dv.toDouble());
				}
			} else {
				Column colm = (Column) gt.getRightExpression();
				if (gt.getLeftExpression() instanceof LongValue) {
					LongValue lv = (LongValue) gt.getLeftExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& lv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), lv.toDouble());
				} else {
					DoubleValue dv = (DoubleValue) gt.getLeftExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& dv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), dv.toDouble());
				}
			}
		} else if (expr instanceof MinorThanEquals) {
			MinorThanEquals gt = (MinorThanEquals) expr;
			if (gt.getLeftExpression() instanceof Column) {
				Column colm = (Column) gt.getLeftExpression();
				if (gt.getRightExpression() instanceof LongValue) {
					LongValue lv = (LongValue) gt.getRightExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& lv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), lv.toDouble());
				} else {
					DoubleValue dv = (DoubleValue) gt.getRightExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& dv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), dv.toDouble());
				}
			} else {
				Column colm = (Column) gt.getRightExpression();
				if (gt.getLeftExpression() instanceof LongValue) {
					LongValue lv = (LongValue) gt.getLeftExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& lv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), lv.toDouble());
				} else {
					DoubleValue dv = (DoubleValue) gt.getLeftExpression();
					if (wheremap.containsKey(colm.getColumnName())
							&& dv.toDouble() == wheremap.get(colm.getColumnName()))
						return false;
					wheremap.put(colm.getColumnName(), dv.toDouble());
				}
			}
		}
		return true;
	}

	private static void twoorderby(List<OrderByElement> orderByElements, List<Expression> expressionList)
			throws SQLException {
		Column col1 = (Column) orderByElements.get(0).getExpression();
		Column col2 = (Column) orderByElements.get(1).getExpression();
		List<Long> finallist = new ArrayList<Long>();
		if (indexnames.contains(col1.getColumnName()) && indexnames.contains(col2.getColumnName())) {

			List<Long> list1;
			if (!orderByElements.get(0).isAsc()) {
				list1 = new ArrayList<Long>(indexMap.get(Main.tableName).get(col1.getColumnName()));
				Collections.reverse(list1);
			} else {
				list1 = indexMap.get(Main.tableName).get(col1.getColumnName());
			}
			List<Long> list2;
			if (!orderByElements.get(1).isAsc()) {
				list2 = new ArrayList<Long>(indexMap.get(Main.tableName).get(col2.getColumnName()));
				Collections.reverse(list2);
			} else {
				list2 = indexMap.get(Main.tableName).get(col2.getColumnName());
			}

			PrimitiveValue prev = null;
			List<Long> local = new ArrayList<Long>();

			for (int i = 0; i < list1.size(); i++) {
				if (!isFull) {
					if (passIdxs.contains(list1.get(i))) {
						Main.valslist = tableData.get(Main.tableName).get(list1.get(i));
						PrimitiveValue val = Main.valslist
								.get(Main.map.get(Main.tableName).get(col1.getColumnName()).firstKey());
						if (val instanceof LongValue) {
							LongValue lval = (LongValue) val;
							LongValue pval;
							if (prev != null)
								pval = (LongValue) prev;
							else
								pval = null;
							indexgroupby(finallist, list1, list2, pval, local, i, lval);
						} else if (val instanceof DoubleValue) {
							DoubleValue lval = (DoubleValue) val;
							DoubleValue pval;
							if (prev != null)
								pval = (DoubleValue) prev;
							else
								pval = null;
							indexgroupby(finallist, list1, list2, pval, local, i, lval);
						} else if (val instanceof StringValue) {
							StringValue lval = (StringValue) val;
							StringValue pval;
							if (prev != null)
								pval = (StringValue) prev;
							else
								pval = null;
							indexgroupby(finallist, list1, list2, pval, local, i, lval);
						} else if (val instanceof DateValue) {
							DateValue lval = (DateValue) val;
							DateValue pval;
							if (prev != null)
								pval = (DateValue) prev;
							else
								pval = null;
							indexgroupby(finallist, list1, list2, pval, local, i, lval);
						}
						prev = val;
					}
				} else {
					Main.valslist = tableData.get(Main.tableName).get(list1.get(i));
					PrimitiveValue val = Main.valslist
							.get(Main.map.get(Main.tableName).get(col1.getColumnName()).firstKey());
					if (val instanceof LongValue) {
						LongValue lval = (LongValue) val;
						LongValue pval;
						if (prev != null)
							pval = (LongValue) prev;
						else
							pval = null;
						indexgroupby(finallist, list1, list2, pval, local, i, lval);
					} else if (val instanceof DoubleValue) {
						DoubleValue lval = (DoubleValue) val;
						DoubleValue pval;
						if (prev != null)
							pval = (DoubleValue) prev;
						else
							pval = null;
						indexgroupby(finallist, list1, list2, pval, local, i, lval);
					} else if (val instanceof StringValue) {
						StringValue lval = (StringValue) val;
						StringValue pval;
						if (prev != null)
							pval = (StringValue) prev;
						else
							pval = null;
						indexgroupby(finallist, list1, list2, pval, local, i, lval);
					} else if (val instanceof DateValue) {
						DateValue lval = (DateValue) val;
						DateValue pval;
						if (prev != null)
							pval = (DateValue) prev;
						else
							pval = null;
						indexgroupby(finallist, list1, list2, pval, local, i, lval);
					}
					prev = val;
				}
			}

			if (local.size() == 1) {
				finallist.add(local.get(0));
				local.clear();
			} else {
				for (int j = 0; j < list2.size(); j++) {
					for (int k = 0; k < local.size(); k++) {
						if (list2.get(j) == local.get(k)) {
							finallist.add(list2.get(j));
							local.remove(k);
							break;
						}
					}
					if (local.size() == 0) {
						break;
					}
				}
			}

			for (int m = 0; m < finallist.size(); m++) {
				Main.valslist = tableData.get(Main.tableName).get(finallist.get(m));
				if (Main.limitcounter == Main.rowCount) {
					break;
				}
				Main.limitcounter++;
				Main.countAggregate++;
				Iterator<Expression> expIter = expressionList.iterator();
				Evaluate evaluate = new Evaluate();
				while (expIter.hasNext()) {
					Expression expr = expIter.next();
					if (expr instanceof Column) {
						String colsum = Main.columnValue(Main.tableName, expr);
						System.out.print(colsum + "|");
					} else if (expr instanceof Function) {
						Main.aggregatesEvaluation(expr);
					} else {
						PrimitiveValue res = evaluate.eval(expr);
						if (res instanceof LongValue) {
							LongValue result = (LongValue) res;
							System.out.print(result.toDouble() + "|");
						} else if (res instanceof DoubleValue) {
							DoubleValue value = (DoubleValue) res;
							System.out.print(value.toDouble() + "|");
						}
					}
				}
				if (Main.isStar) {
					for (int k = 0; k < Main.valslist.size(); k++) {
						if (Main.valslist.get(k) instanceof StringValue) {
							StringValue sv = (StringValue) Main.valslist.get(k);
							System.out.print(sv.getValue() + "|");
						} else
							System.out.print(Main.valslist.get(k) + "|");
					}
				}
				if (!Main.isAggregateExpression)
					System.out.println();
			}
		} else {
			// If both are not indexes
			List<List<PrimitiveValue>> localdata = new ArrayList<List<PrimitiveValue>>();
			Map<Long, List<PrimitiveValue>> localmap = tableData.get(Main.tableName);
			if (isFull)
				passIdxs = tableData.get(Main.tableName).keySet();
			for (Long value : passIdxs) {
				localdata.add(localmap.get(value));
			}

			ArrayList<Datatypes> coldatatypes = new ArrayList<Datatypes>();
			coldatatypes.add(Main.map.get(Main.tableName).get(col1.getColumnName()).firstEntry().getValue());
			coldatatypes.add(Main.map.get(Main.tableName).get(col2.getColumnName()).firstEntry().getValue());

			ArrayList<Integer> colindexes = new ArrayList<Integer>();
			colindexes.add(Main.map.get(Main.tableName).get(col1.getColumnName()).firstKey());
			colindexes.add(Main.map.get(Main.tableName).get(col2.getColumnName()).firstKey());

			ExternalSort.sortColDataTypes = coldatatypes;
			ExternalSort.sortColIndexes = colindexes;
			List<Boolean> sorttypes = new ArrayList<Boolean>(Arrays.asList(true, true));
			if (!orderByElements.get(0).isAsc())
				sorttypes.set(0, false);
			if (!orderByElements.get(1).isAsc())
				sorttypes.set(1, false);
			ExternalSort.sortType = sorttypes;
			Collections.sort(localdata, new ExternalSort.muliplecolscomppv());
			for (int i = 0; i < localdata.size(); i++) {

				Main.valslist = localdata.get(i);
				if (Main.limitcounter == Main.rowCount) {
					break;
				}
				Main.limitcounter++;
				Main.countAggregate++;
				Iterator<Expression> expIter = expressionList.iterator();
				Evaluate evaluate = new Evaluate();
				while (expIter.hasNext()) {
					Expression expr = expIter.next();
					if (expr instanceof Column) {
						String colsum = Main.columnValue(Main.tableName, expr);
						System.out.print(colsum + "|");
					} else if (expr instanceof Function) {
						Main.aggregatesEvaluation(expr);
					} else {
						PrimitiveValue res = evaluate.eval(expr);
						if (res instanceof LongValue) {
							LongValue result = (LongValue) res;
							System.out.print(result.toDouble() + "|");
						} else if (res instanceof DoubleValue) {
							DoubleValue value = (DoubleValue) res;
							System.out.print(value.toDouble() + "|");
						}
					}
				}
				if (Main.isStar) {
					for (int k = 0; k < Main.valslist.size(); k++) {
						if (Main.valslist.get(k) instanceof StringValue) {
							StringValue sv = (StringValue) Main.valslist.get(k);
							System.out.print(sv.getValue() + "|");
						} else
							System.out.print(Main.valslist.get(k) + "|");
					}
				}
				if (!Main.isAggregateExpression)
					System.out.println();
			}
			localdata.clear();
		}
	}

	private static void singleorderby(List<OrderByElement> orderByElements, List<Expression> expressionList)
			throws SQLException {
		Column col = (Column) orderByElements.get(0).getExpression();
		if (indexnames.contains(col.getColumnName())) {
			List<Long> ci;
			if (!orderByElements.get(0).isAsc()) {
				ci = new ArrayList<Long>(indexMap.get(Main.tableName).get(col.getColumnName()));
				Collections.reverse(ci);
			} else {
				ci = indexMap.get(Main.tableName).get(col.getColumnName());
			}

			for (int i = 0; i < ci.size(); i++) {
				if (!isFull) {
					if (passIdxs.contains(ci.get(i))) {
						Main.valslist = tableData.get(Main.tableName).get(ci.get(i));
						if (Main.limitcounter == Main.rowCount) {
							break;
						}
						Main.limitcounter++;
						Main.countAggregate++;
						Iterator<Expression> expIter = expressionList.iterator();
						Evaluate evaluate = new Evaluate();
						while (expIter.hasNext()) {
							Expression expr = expIter.next();
							if (expr instanceof Column) {
								String colsum = Main.columnValue(Main.tableName, expr);
								System.out.print(colsum + "|");
							} else if (expr instanceof Function) {
								Main.aggregatesEvaluation(expr);
							} else {
								PrimitiveValue res = evaluate.eval(expr);
								if (res instanceof LongValue) {
									LongValue result = (LongValue) res;
									System.out.print(result.toDouble() + "|");
								} else if (res instanceof DoubleValue) {
									DoubleValue value = (DoubleValue) res;
									System.out.print(value.toDouble() + "|");
								}
							}
						}
						if (Main.isStar) {
							for (int k = 0; k < Main.valslist.size(); k++) {
								if (Main.valslist.get(k) instanceof StringValue) {
									StringValue sv = (StringValue) Main.valslist.get(k);
									System.out.print(sv.getValue() + "|");
								} else
									System.out.print(Main.valslist.get(k) + "|");
							}
						}
						if (!Main.isAggregateExpression)
							System.out.println();
					}
				} else {
					Main.valslist = tableData.get(Main.tableName).get(ci.get(i));
					if (Main.limitcounter == Main.rowCount) {
						break;
					}
					Main.limitcounter++;
					Main.countAggregate++;
					Iterator<Expression> expIter = expressionList.iterator();
					Evaluate evaluate = new Evaluate();
					while (expIter.hasNext()) {
						Expression expr = expIter.next();
						if (expr instanceof Column) {
							String colsum = Main.columnValue(Main.tableName, expr);
							System.out.print(colsum + "|");
						} else if (expr instanceof Function) {
							Main.aggregatesEvaluation(expr);
						} else {
							PrimitiveValue res = evaluate.eval(expr);
							if (res instanceof LongValue) {
								LongValue result = (LongValue) res;
								System.out.print(result.toDouble() + "|");
							} else if (res instanceof DoubleValue) {
								DoubleValue value = (DoubleValue) res;
								System.out.print(value.toDouble() + "|");
							}
						}
					}
					if (Main.isStar) {
						for (int k = 0; k < Main.valslist.size(); k++) {
							if (Main.valslist.get(k) instanceof StringValue) {
								StringValue sv = (StringValue) Main.valslist.get(k);
								System.out.print(sv.getValue() + "|");
							} else
								System.out.print(Main.valslist.get(k) + "|");
						}
					}
					if (!Main.isAggregateExpression)
						System.out.println();
				}
			}
		} else {
			// If its not an index
			List<List<PrimitiveValue>> localdata = new ArrayList<List<PrimitiveValue>>();
			Map<Long, List<PrimitiveValue>> localmap = tableData.get(Main.tableName);

			for (Long value : passIdxs) {
				localdata.add(localmap.get(value));
			}

			ExternalSort.sortColDataTypes = new ArrayList<Datatypes>(
					Arrays.asList(Main.map.get(Main.tableName).get(col.getColumnName()).firstEntry().getValue()));
			ExternalSort.sortColIndexes = new ArrayList<Integer>(
					Arrays.asList(Main.map.get(Main.tableName).get(col.getColumnName()).firstKey()));
			if (!orderByElements.get(0).isAsc())
				ExternalSort.sortType = new ArrayList<Boolean>(Arrays.asList(false));
			else
				ExternalSort.sortType = new ArrayList<Boolean>(Arrays.asList(true));
			Collections.sort(localdata, new ExternalSort.muliplecolscomppv());

			for (int i = 0; i < localdata.size(); i++) {
				Main.valslist = localdata.get(i);
				if (Main.limitcounter == Main.rowCount) {
					break;
				}
				Main.limitcounter++;
				Main.countAggregate++;
				Iterator<Expression> expIter = expressionList.iterator();
				Evaluate evaluate = new Evaluate();
				while (expIter.hasNext()) {
					Expression expr = expIter.next();
					if (expr instanceof Column) {
						String colsum = Main.columnValue(Main.tableName, expr);
						System.out.print(colsum + "|");
					} else if (expr instanceof Function) {
						Main.aggregatesEvaluation(expr);
					} else {
						PrimitiveValue res = evaluate.eval(expr);
						if (res instanceof LongValue) {
							LongValue result = (LongValue) res;
							System.out.print(result.toDouble() + "|");
						} else if (res instanceof DoubleValue) {
							DoubleValue value = (DoubleValue) res;
							System.out.print(value.toDouble() + "|");
						}
					}
				}
				if (Main.isStar) {
					for (int k = 0; k < Main.valslist.size(); k++) {
						if (Main.valslist.get(k) instanceof StringValue) {
							StringValue sv = (StringValue) Main.valslist.get(k);
							System.out.print(sv.getValue() + "|");
						} else
							System.out.print(Main.valslist.get(k) + "|");
					}
				}
				if (!Main.isAggregateExpression)
					System.out.println();
			}
		}
	}

	private static void bothgroupbyorderbyeval(List<Column> groupByExpr, List<OrderByElement> orderByElements,
			List<Expression> expressionList) throws SQLException {
		if (groupByExpr.size() == 1) {
			String colName = groupByExpr.get(0).getColumnName();
			if (indexnames.contains(colName)) {
				List<Long> gi;
				if (!orderByElements.get(0).isAsc()) {
					gi = new ArrayList<Long>(indexMap.get(Main.tableName).get(colName));
					Collections.reverse(gi);
				} else {
					gi = indexMap.get(Main.tableName).get(colName);
				}

				for (int i = 0; i < gi.size(); i++) {
					if (!isFull) {
						if (passIdxs.contains(gi.get(i))) {
							Main.valslist = tableData.get(Main.tableName).get(gi.get(i));
							if (Main.limitcounter == Main.rowCount)
								break;
							String res = "";
							Main.onlygroupby(groupByExpr, expressionList, res);
							continue;
						}
					} else {
						Main.valslist = tableData.get(Main.tableName).get(gi.get(i));
						if (Main.limitcounter == Main.rowCount)
							break;
						String res = "";
						Main.onlygroupby(groupByExpr, expressionList, res);
						continue;
					}
				}
			} else {

				List<List<PrimitiveValue>> localdata = new ArrayList<List<PrimitiveValue>>();
				Map<Long, List<PrimitiveValue>> localmap = tableData.get(Main.tableName);

				for (Long value : passIdxs) {
					localdata.add(localmap.get(value));
				}

				ExternalSort.sortColDataTypes = new ArrayList<Datatypes>(
						Arrays.asList(Main.map.get(Main.tableName).get(colName).firstEntry().getValue()));
				ExternalSort.sortColIndexes = new ArrayList<Integer>(
						Arrays.asList(Main.map.get(Main.tableName).get(colName).firstKey()));
				if (!orderByElements.get(0).isAsc())
					ExternalSort.sortType = new ArrayList<Boolean>(Arrays.asList(false));
				else
					ExternalSort.sortType = new ArrayList<Boolean>(Arrays.asList(true));
				Collections.sort(localdata, new ExternalSort.muliplecolscomppv());
				for (int i = 0; i < localdata.size(); i++) {

					Main.valslist = localdata.get(i);
					if (Main.limitcounter == Main.rowCount)
						break;
					String res = "";
					Main.onlygroupby(groupByExpr, expressionList, res);
					continue;
				}
				localdata.clear();

			}
		} else if (groupByExpr.size() == 2) {

			if (orderByElements.size() == 2) {

				String colName1 = groupByExpr.get(0).getColumnName();
				String colName2 = groupByExpr.get(1).getColumnName();
				List<Long> finallist = new ArrayList<Long>();
				if (indexnames.contains(colName1) && indexnames.contains(colName2)) {

					List<Long> list1;
					if (!orderByElements.get(0).isAsc()) {
						list1 = new ArrayList<Long>(indexMap.get(Main.tableName).get(colName1));
						Collections.reverse(list1);
					} else {
						list1 = indexMap.get(Main.tableName).get(colName1);
					}
					List<Long> list2;
					if (!orderByElements.get(1).isAsc()) {
						list2 = new ArrayList<Long>(indexMap.get(Main.tableName).get(colName2));
						Collections.reverse(list2);
					} else {
						list2 = indexMap.get(Main.tableName).get(colName2);
					}

					PrimitiveValue prev = null;
					List<Long> local = new ArrayList<Long>();

					for (int i = 0; i < list1.size(); i++) {
						if (!isFull) {
							if (passIdxs.contains(list1.get(i))) {
								Main.valslist = tableData.get(Main.tableName).get(list1.get(i));
								PrimitiveValue val = Main.valslist
										.get(Main.map.get(Main.tableName).get(colName1).firstKey());
								if (val instanceof LongValue) {
									LongValue lval = (LongValue) val;
									LongValue pval;
									if (prev != null)
										pval = (LongValue) prev;
									else
										pval = null;
									indexgroupby(finallist, list1, list2, pval, local, i, lval);
								} else if (val instanceof DoubleValue) {
									DoubleValue lval = (DoubleValue) val;
									DoubleValue pval;
									if (prev != null)
										pval = (DoubleValue) prev;
									else
										pval = null;
									indexgroupby(finallist, list1, list2, pval, local, i, lval);
								} else if (val instanceof StringValue) {
									StringValue lval = (StringValue) val;
									StringValue pval;
									if (prev != null)
										pval = (StringValue) prev;
									else
										pval = null;
									indexgroupby(finallist, list1, list2, pval, local, i, lval);
								} else if (val instanceof DateValue) {
									DateValue lval = (DateValue) val;
									DateValue pval;
									if (prev != null)
										pval = (DateValue) prev;
									else
										pval = null;
									indexgroupby(finallist, list1, list2, pval, local, i, lval);
								}
								prev = val;
							}

						} else {
							Main.valslist = tableData.get(Main.tableName).get(list1.get(i));
							PrimitiveValue val = Main.valslist
									.get(Main.map.get(Main.tableName).get(colName1).firstKey());
							if (val instanceof LongValue) {
								LongValue lval = (LongValue) val;
								LongValue pval;
								if (prev != null)
									pval = (LongValue) prev;
								else
									pval = null;
								indexgroupby(finallist, list1, list2, pval, local, i, lval);
							} else if (val instanceof DoubleValue) {
								DoubleValue lval = (DoubleValue) val;
								DoubleValue pval;
								if (prev != null)
									pval = (DoubleValue) prev;
								else
									pval = null;
								indexgroupby(finallist, list1, list2, pval, local, i, lval);
							} else if (val instanceof StringValue) {
								StringValue lval = (StringValue) val;
								StringValue pval;
								if (prev != null)
									pval = (StringValue) prev;
								else
									pval = null;
								indexgroupby(finallist, list1, list2, pval, local, i, lval);
							} else if (val instanceof DateValue) {
								DateValue lval = (DateValue) val;
								DateValue pval;
								if (prev != null)
									pval = (DateValue) prev;
								else
									pval = null;
								indexgroupby(finallist, list1, list2, pval, local, i, lval);
							}
							prev = val;
						}
					}

					if (local.size() == 1) {
						finallist.add(local.get(0));
						local.clear();
					} else {
						for (int j = 0; j < list2.size(); j++) {
							for (int k = 0; k < local.size(); k++) {
								if (list2.get(j) == local.get(k)) {
									finallist.add(list2.get(j));
									local.remove(k);
									break;
								}
							}
							if (local.size() == 0) {
								break;
							}
						}
					}

					for (int m = 0; m < finallist.size(); m++) {
						Main.valslist = tableData.get(Main.tableName).get(finallist.get(m));
						if (Main.limitcounter == Main.rowCount)
							break;
						String res = "";
						Main.onlygroupby(groupByExpr, expressionList, res);
						continue;
					}
				} else {
					// If both are not indexes
					List<List<PrimitiveValue>> localdata = new ArrayList<List<PrimitiveValue>>();
					Map<Long, List<PrimitiveValue>> localmap = tableData.get(Main.tableName);

					for (Long value : passIdxs) {
						localdata.add(localmap.get(value));
					}

					ArrayList<Datatypes> coldatatypes = new ArrayList<Datatypes>();
					coldatatypes.add(Main.map.get(Main.tableName).get(groupByExpr.get(0).getColumnName()).firstEntry()
							.getValue());
					coldatatypes.add(Main.map.get(Main.tableName).get(groupByExpr.get(1).getColumnName()).firstEntry()
							.getValue());

					ArrayList<Integer> colindexes = new ArrayList<Integer>();
					colindexes.add(Main.map.get(Main.tableName).get(groupByExpr.get(0).getColumnName()).firstKey());
					colindexes.add(Main.map.get(Main.tableName).get(groupByExpr.get(1).getColumnName()).firstKey());

					ExternalSort.sortColDataTypes = coldatatypes;
					ExternalSort.sortColIndexes = colindexes;
					List<Boolean> sorttypes = new ArrayList<Boolean>(Arrays.asList(true, true));
					if (!orderByElements.get(0).isAsc())
						sorttypes.set(0, false);
					if (!orderByElements.get(1).isAsc())
						sorttypes.set(1, false);
					ExternalSort.sortType = sorttypes;
					Collections.sort(localdata, new ExternalSort.muliplecolscomppv());
					for (int i = 0; i < localdata.size(); i++) {

						Main.valslist = localdata.get(i);
						if (Main.limitcounter == Main.rowCount)
							break;
						String res = "";
						Main.onlygroupby(groupByExpr, expressionList, res);
						continue;
					}
					localdata.clear();
				}
			}

		}
	}

	private static void onlygroupByEvaluation(List<Column> groupByExpr, List<Expression> expressionList)
			throws SQLException {
		if (groupByExpr.size() == 1) {
			String colName = groupByExpr.get(0).getColumnName();
			if (indexnames.contains(colName)) {
				List<Long> gi = indexMap.get(Main.tableName).get(colName);
				for (int i = 0; i < gi.size(); i++) {

					if (!isFull) {
						if (passIdxs.contains(gi.get(i))) {
							Main.valslist = tableData.get(Main.tableName).get(gi.get(i));
							if (Main.limitcounter == Main.rowCount)
								break;
							String res = "";
							Main.onlygroupby(groupByExpr, expressionList, res);
							continue;
						}
					} else {
						Main.valslist = tableData.get(Main.tableName).get(gi.get(i));
						if (Main.limitcounter == Main.rowCount)
							break;
						String res = "";
						Main.onlygroupby(groupByExpr, expressionList, res);
						continue;
					}

				}
			} else {
				// If its not an index
				List<List<PrimitiveValue>> localdata = new ArrayList<List<PrimitiveValue>>();
				Map<Long, List<PrimitiveValue>> localmap = tableData.get(Main.tableName);

				for (Long value : passIdxs) {
					localdata.add(localmap.get(value));
				}

				ExternalSort.sortColDataTypes = new ArrayList<Datatypes>(
						Arrays.asList(Main.map.get(Main.tableName).get(colName).firstEntry().getValue()));
				ExternalSort.sortColIndexes = new ArrayList<Integer>(
						Arrays.asList(Main.map.get(Main.tableName).get(colName).firstKey()));
				ExternalSort.sortType = new ArrayList<Boolean>(Arrays.asList(true));
				Collections.sort(localdata, new ExternalSort.muliplecolscomppv());
				for (int i = 0; i < localdata.size(); i++) {

					Main.valslist = localdata.get(i);
					if (Main.limitcounter == Main.rowCount)
						break;
					String res = "";
					Main.onlygroupby(groupByExpr, expressionList, res);
					continue;
				}
				localdata.clear();
			}
		} else if (groupByExpr.size() == 2) {

			String colName1 = groupByExpr.get(0).getColumnName();
			String colName2 = groupByExpr.get(1).getColumnName();
			List<Long> finallist = new ArrayList<Long>();
			if (indexnames.contains(colName1) && indexnames.contains(colName2)) {
				List<Long> list1 = indexMap.get(Main.tableName).get(colName1);
				List<Long> list2 = indexMap.get(Main.tableName).get(colName2);
				PrimitiveValue prev = null;
				List<Long> local = new ArrayList<Long>();

				for (int i = 0; i < list1.size(); i++) {
					if (!isFull) {
						if (passIdxs.contains(list1.get(i))) {
							Main.valslist = tableData.get(Main.tableName).get(list1.get(i));
							PrimitiveValue val = Main.valslist
									.get(Main.map.get(Main.tableName).get(colName1).firstKey());
							if (val instanceof LongValue) {
								LongValue lval = (LongValue) val;
								LongValue pval;
								if (prev != null)
									pval = (LongValue) prev;
								else
									pval = null;
								indexgroupby(finallist, list1, list2, pval, local, i, lval);
							} else if (val instanceof DoubleValue) {
								DoubleValue lval = (DoubleValue) val;
								DoubleValue pval;
								if (prev != null)
									pval = (DoubleValue) prev;
								else
									pval = null;
								indexgroupby(finallist, list1, list2, pval, local, i, lval);
							} else if (val instanceof StringValue) {
								StringValue lval = (StringValue) val;
								StringValue pval;
								if (prev != null)
									pval = (StringValue) prev;
								else
									pval = null;
								indexgroupby(finallist, list1, list2, pval, local, i, lval);
							} else if (val instanceof DateValue) {
								DateValue lval = (DateValue) val;
								DateValue pval;
								if (prev != null)
									pval = (DateValue) prev;
								else
									pval = null;
								indexgroupby(finallist, list1, list2, pval, local, i, lval);
							}
							prev = val;
						}
					} else {

						Main.valslist = tableData.get(Main.tableName).get(list1.get(i));
						PrimitiveValue val = Main.valslist.get(Main.map.get(Main.tableName).get(colName1).firstKey());
						if (val instanceof LongValue) {
							LongValue lval = (LongValue) val;
							LongValue pval;
							if (prev != null)
								pval = (LongValue) prev;
							else
								pval = null;
							indexgroupby(finallist, list1, list2, pval, local, i, lval);
						} else if (val instanceof DoubleValue) {
							DoubleValue lval = (DoubleValue) val;
							DoubleValue pval;
							if (prev != null)
								pval = (DoubleValue) prev;
							else
								pval = null;
							indexgroupby(finallist, list1, list2, pval, local, i, lval);
						} else if (val instanceof StringValue) {
							StringValue lval = (StringValue) val;
							StringValue pval;
							if (prev != null)
								pval = (StringValue) prev;
							else
								pval = null;
							indexgroupby(finallist, list1, list2, pval, local, i, lval);
						} else if (val instanceof DateValue) {
							DateValue lval = (DateValue) val;
							DateValue pval;
							if (prev != null)
								pval = (DateValue) prev;
							else
								pval = null;
							indexgroupby(finallist, list1, list2, pval, local, i, lval);
						}
						prev = val;

					}

				}

				if (local.size() == 1) {
					finallist.add(local.get(0));
					local.clear();
				} else {
					for (int j = 0; j < list2.size(); j++) {
						for (int k = 0; k < local.size(); k++) {
							if (list2.get(j) == local.get(k)) {
								finallist.add(list2.get(j));
								local.remove(k);
								break;
							}
						}
						if (local.size() == 0) {
							break;
						}
					}
				}

				for (int m = 0; m < finallist.size(); m++) {
					Main.valslist = tableData.get(Main.tableName).get(finallist.get(m));
					if (Main.limitcounter == Main.rowCount)
						break;
					String res = "";
					Main.onlygroupby(groupByExpr, expressionList, res);
					continue;
				}

			} else {
				// If both are not indexes
				List<List<PrimitiveValue>> localdata = new ArrayList<List<PrimitiveValue>>();
				Map<Long, List<PrimitiveValue>> localmap = tableData.get(Main.tableName);

				for (Long value : passIdxs) {
					localdata.add(localmap.get(value));
				}

				ArrayList<Datatypes> coldatatypes = new ArrayList<Datatypes>();
				coldatatypes.add(
						Main.map.get(Main.tableName).get(groupByExpr.get(0).getColumnName()).firstEntry().getValue());
				coldatatypes.add(
						Main.map.get(Main.tableName).get(groupByExpr.get(1).getColumnName()).firstEntry().getValue());

				ArrayList<Integer> colindexes = new ArrayList<Integer>();
				colindexes.add(Main.map.get(Main.tableName).get(groupByExpr.get(0).getColumnName()).firstKey());
				colindexes.add(Main.map.get(Main.tableName).get(groupByExpr.get(1).getColumnName()).firstKey());

				ExternalSort.sortColDataTypes = coldatatypes;
				ExternalSort.sortColIndexes = colindexes;
				ExternalSort.sortType = new ArrayList<Boolean>(Arrays.asList(true, true));
				Collections.sort(localdata, new ExternalSort.muliplecolscomppv());
				for (int i = 0; i < localdata.size(); i++) {

					Main.valslist = localdata.get(i);
					if (Main.limitcounter == Main.rowCount)
						break;
					String res = "";
					Main.onlygroupby(groupByExpr, expressionList, res);
					continue;
				}
				localdata.clear();
			}
		}
	}

	private static void indexgroupby(List<Long> finallist, List<Long> list1, List<Long> list2, PrimitiveValue prev,
			List<Long> local, int i, PrimitiveValue val) {
		if (prev == null || prev.equals(val)) {
			local.add(list1.get(i));
		} else {

			if (local.size() == 1) {
				finallist.add(local.get(0));
				local.clear();
			} else {
				for (int j = 0; j < list2.size(); j++) {
					for (int k = 0; k < local.size(); k++) {
						if (list2.get(j) == local.get(k)) {
							finallist.add(list2.get(j));
							local.remove(k);
							break;
						}
					}
					if (local.size() == 0) {
						break;
					}
				}
			}

			local.add(list1.get(i));
		}
	}

	public static void buildIndexes(CreateTable table) throws IOException, InvalidPrimitive {

		BufferedReader br;

		String pk = "";
		String pk2 = "";
		String tableName = table.getTable().getName();
		List<Index> indexes = table.getIndexes();
		for (int i = 0; i < indexes.size(); i++) {
			Index idx = indexes.get(i);
			if (idx.getType().equals("PRIMARY KEY")) {
				pk = idx.getColumnsNames().get(0);
				if (idx.getColumnsNames().size() > 1) {
					pk2 = idx.getColumnsNames().get(1);
				} else {
					if (!projs.containsKey(tableName))
						projs.put(tableName, new HashSet<String>(Arrays.asList(pk)));
					else
						projs.get(tableName).add(pk);
				}
				continue;
			}
		}

		Map<String, List<IndexData>> lmap = new HashMap<String, List<IndexData>>();
		br = new BufferedReader(new FileReader("data/" + tableName + ".csv"));
		String line = "";
		String[] vals;
		long pvalc = 0;
		while ((line = br.readLine()) != null) {
			vals = line.split("\\|");

			List<PrimitiveValue> llist = new ArrayList<PrimitiveValue>(13);
			for (int i = 0; i < vals.length; i++) {
				if (coldatatypes.get(i) == Datatypes.INT) {
					llist.add(new LongValue(vals[i]));
				} else if (coldatatypes.get(i) == Datatypes.DECIMAL) {
					llist.add(new DoubleValue(vals[i]));
				} else if (coldatatypes.get(i) == Datatypes.CHAR) {
					llist.add(new StringValue(vals[i]));
				} else if (coldatatypes.get(i) == Datatypes.STRING) {
					llist.add(new StringValue(vals[i]));
				} else if (coldatatypes.get(i) == Datatypes.DATE) {
					llist.add(new DateValue(vals[i]));
				} else if (coldatatypes.get(i) == Datatypes.VARCHAR) {
					llist.add(new StringValue(vals[i]));
				}
			}
			PrimitiveValue pval = llist.get(Main.map.get(tableName).get(pk).firstKey());

			if (!pk2.isEmpty()) {
				pvalc++;
			}
			if (tableData.containsKey(tableName)) {
				if (pvalc == 0) {
					tableData.get(tableName).put(pval.toLong(), llist);
				} else {
					tableData.get(tableName).put(pvalc, llist);
				}
			} else {
				LinkedHashMap<Long, List<PrimitiveValue>> lomap = new LinkedHashMap<Long, List<PrimitiveValue>>();
				if (pvalc == 0) {
					lomap.put(pval.toLong(), llist);
				} else {
					lomap.put(pvalc, llist);
				}
				tableData.put(tableName, lomap);
			}

			if (!referenceIndxs.isEmpty() && referenceIndxs.containsKey(tableName)) {
				for (String colname : referenceIndxs.get(tableName)) {
					PrimitiveValue lval = llist.get(Main.map.get(tableName).get(colname).firstKey());
					if (lmap.containsKey(colname)) {
						if (pvalc == 0) {
							lmap.get(colname).add(new IndexData(pval.toLong(), lval));
						} else
							lmap.get(colname).add(new IndexData(pvalc, lval));
					} else {
						List<IndexData> data = new ArrayList<IndexData>();
						if (pvalc == 0)
							data.add(new IndexData(pval.toLong(), lval));
						else
							data.add(new IndexData(pvalc, lval));
						lmap.put(colname, data);
					}
				}
			}
		}
		br.close();
		if (!lmap.isEmpty()) {
			for (Map.Entry<String, List<IndexData>> entry : lmap.entrySet()) {
				List<IndexData> dt = entry.getValue();
				sortValues(dt);
				List<Long> pidxs = new ArrayList<Long>();
				for (int i = 0; i < dt.size(); i++) {
					pidxs.add(dt.get(i).key);
				}
				if (indexMap.containsKey(tableName)) {
					indexMap.get(tableName).put(entry.getKey(), pidxs);
				} else {
					Map<String, List<Long>> vmap = new HashMap<String, List<Long>>();
					vmap.put(entry.getKey(), pidxs);
					indexMap.put(tableName, vmap);
				}
			}
		}
		lmap.clear();

	}

	private static void commonCols(String tablename, List<ColumnDefinition> columns) {

		if (tablename.equals("ORDERS")) {
			TreeMap<String, String> lmap = new TreeMap<String, String>();
			lmap.put("CUSTOMER", "CUSTKEY");
			commoncolmap.put(tablename, lmap);
			if (!projs.containsKey(tablename))
				projs.put(tablename, new HashSet<String>(Arrays.asList("CUSTKEY")));
			else
				projs.get(tablename).add("CUSTKEY");
			referenceIndxs.put(tablename, new HashSet<String>(Arrays.asList("CUSTKEY")));
		} else if (tablename.equals("LINEITEM")) {
			TreeMap<String, String> lmap1 = new TreeMap<String, String>();
			lmap1.put("ORDERS", "ORDERKEY");
			commoncolmap.put(tablename, lmap1);
			commoncolmap.get(tablename).put("PART", "PARTKEY");
			commoncolmap.get(tablename).put("SUPPLIER", "SUPPKEY");
			if (!projs.containsKey(tablename))
				projs.put(tablename, new HashSet<String>(Arrays.asList("ORDERKEY")));
			else
				projs.get(tablename).add("ORDERKEY");
			projs.get(tablename).add("PARTKEY");
			projs.get(tablename).add("SUPPKEY");
			referenceIndxs.put(tablename, new HashSet<String>(Arrays.asList("ORDERKEY")));
			referenceIndxs.get(tablename).add("PARTKEY");
			referenceIndxs.get(tablename).add("SUPPKEY");
		} else if (tablename.equals("SUPPLIER")) {
			TreeMap<String, String> lmap = new TreeMap<String, String>();
			lmap.put("NATION", "NATIONKEY");
			commoncolmap.put(tablename, lmap);
			if (!projs.containsKey(tablename))
				projs.put(tablename, new HashSet<String>(Arrays.asList("NATIONKEY")));
			else
				projs.get(tablename).add("NATIONKEY");
			referenceIndxs.put(tablename, new HashSet<String>(Arrays.asList("NATIONKEY")));
		} else if (tablename.equals("NATION")) {
			TreeMap<String, String> lmap = new TreeMap<String, String>();
			lmap.put("REGION", "REGIONKEY");
			commoncolmap.put(tablename, lmap);
			if (!projs.containsKey(tablename))
				projs.put(tablename, new HashSet<String>(Arrays.asList("REGIONKEY")));
			else
				projs.get(tablename).add("REGIONKEY");
			referenceIndxs.put(tablename, new HashSet<String>(Arrays.asList("REGIONKEY")));
		} else if (tablename.equals("PARTSUPP")) {
			TreeMap<String, String> lmap1 = new TreeMap<String, String>();
			lmap1.put("PART", "PARTKEY");
			commoncolmap.put(tablename, lmap1);
			commoncolmap.get(tablename).put("SUPPLIER", "SUPPKEY");
			if (!projs.containsKey(tablename))
				projs.put(tablename, new HashSet<String>(Arrays.asList("PARTKEY")));
			else
				projs.get(tablename).add("PARTKEY");
			referenceIndxs.put(tablename, new HashSet<String>(Arrays.asList("PARTKEY")));
			projs.get(tablename).add("SUPPKEY");
			referenceIndxs.get(tablename).add("SUPPKEY");
		} else if (tablename.equals("CUSTOMER")) {
			TreeMap<String, String> lmap = new TreeMap<String, String>();
			lmap.put("NATION", "NATIONKEY");
			commoncolmap.put(tablename, lmap);
			if (!projs.containsKey(tablename))
				projs.put(tablename, new HashSet<String>(Arrays.asList("NATIONKEY")));
			else
				projs.get(tablename).add("NATIONKEY");
			referenceIndxs.put(tablename, new HashSet<String>(Arrays.asList("NATIONKEY")));
		}
	}

	public static void sortValues(List<IndexData> list) {

		Collections.sort(list, new MyIndexComp());

	}

	public static void columnInfo(List<ColumnDefinition> columns, Map<String, TreeMap<Integer, Datatypes>> cmap,
			String tablename) {
		for (int i = 0; i < columns.size(); i++) {
			TreeMap<Integer, Datatypes> indexType = new TreeMap<Integer, Datatypes>();
			String dType = columns.get(i).getColDataType().getDataType();
			Datatypes enumDataType = Datatypes.UNKNOWN;
			if (dType.equalsIgnoreCase("int")) {
				enumDataType = Datatypes.INT;
			} else if (dType.equalsIgnoreCase("string")) {
				enumDataType = Datatypes.STRING;
			} else if (dType.equalsIgnoreCase("decimal")) {
				enumDataType = Datatypes.DECIMAL;
			} else if (dType.equalsIgnoreCase("varchar")) {
				enumDataType = Datatypes.VARCHAR;
			} else if (dType.equalsIgnoreCase("char")) {
				enumDataType = Datatypes.CHAR;
			} else if (dType.equalsIgnoreCase("date")) {
				enumDataType = Datatypes.DATE;
			}
			indexType.put(i, enumDataType);
			cmap.put(columns.get(i).getColumnName(), indexType);
			coldatatypes.add(enumDataType);
			if (!tabcoldatattypes.containsKey(tablename)) {
				tabcoldatattypes.put(tablename, new ArrayList<Datatypes>(Arrays.asList(enumDataType)));
			} else
				tabcoldatattypes.get(tablename).add(enumDataType);
			if (!tabcolnames.containsKey(tablename)) {
				tabcolnames.put(tablename, new ArrayList<String>(Arrays.asList(columns.get(i).getColumnName())));
			} else
				tabcolnames.get(tablename).add(columns.get(i).getColumnName());
		}
	}

	public static void main(String[] args) throws IOException, SQLException {
		InMemory.evaluateInMem();
		System.out.println();
	}

	static class MyIndexComp implements Comparator<IndexData> {

		@Override
		public int compare(IndexData arg0, IndexData arg1) {

			try {
				if (arg0.value.toDouble() - arg1.value.toDouble() > 0)
					return 1;
				else if (arg0.value.toDouble() - arg1.value.toDouble() < 0)
					return -1;
			} catch (InvalidPrimitive e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			return 0;
		}
	}

	static class MyMultipleIndexComp implements Comparator<MultipleIndexData> {

		@Override
		public int compare(MultipleIndexData arg0, MultipleIndexData arg1) {

			try {
				if (arg0.value1.toDouble() - arg1.value1.toDouble() > 0)
					return 1;
				else if (arg0.value1.toDouble() - arg1.value1.toDouble() < 0)
					return -1;
			} catch (InvalidPrimitive e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			try {
				if (arg0.value2.toDouble() - arg1.value2.toDouble() > 0)
					return 1;
				else if (arg0.value2.toDouble() - arg1.value2.toDouble() < 0)
					return -1;
			} catch (InvalidPrimitive e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			return 0;
		}
	}
}

class IndexData {

	long key;
	PrimitiveValue value;

	public IndexData(long key, PrimitiveValue value) {
		this.key = key;
		this.value = value;
	}
}

class MultipleIndexData {

	long key;
	PrimitiveValue value1;
	PrimitiveValue value2;

	public MultipleIndexData(long key, PrimitiveValue value1, PrimitiveValue value2) {
		this.key = key;
		this.value1 = value1;
		this.value2 = value2;
	}

}