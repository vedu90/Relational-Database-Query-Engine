package dubstep;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringReader;
import java.sql.SQLException;
import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.TreeMap;

import dubstep.Main.Datatypes;
import dubstep.OnDisk.colDataType;
import net.sf.jsqlparser.expression.CaseExpression;
import net.sf.jsqlparser.expression.DateValue;
import net.sf.jsqlparser.expression.DoubleValue;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.expression.Function;
import net.sf.jsqlparser.expression.LongValue;
import net.sf.jsqlparser.expression.PrimitiveValue;
import net.sf.jsqlparser.expression.StringValue;
import net.sf.jsqlparser.expression.WhenClause;
import net.sf.jsqlparser.expression.operators.arithmetic.Addition;
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

public class OnDisk {
	
	static class tableLength{
		Long tableSize;
		String tabName;
		tableLength(Long l,String t){
			this.tableSize = l;
			this.tabName= t;
		}
	}
	
	static class JoinPair{
		String table1;
		String table2;
		String joinCol;
		JoinPair(String t1,String t2,String j){
			this.table1 = t1;
			this.table2 = t2;
			this.joinCol = j;
		}
	}
	public static class colDataType{
		Datatypes dtype;
		int ind;
		colDataType(int i,Datatypes d){
			this.ind = i;
			this.dtype = d;
		}
	}
	public static class toSortTableData{
		String tName;
		String tCol;
		toSortTableData(String name,String col){
			this.tName=name;
			this.tCol = col;
		}
	}
	
	public static class sortTables implements Comparator<tableLength>{
		public int compare(tableLength t1, tableLength t2){
			if(t1.tableSize>t2.tableSize){
				return 1;
			}
			return -1;
		}
	}
	
	public static class tableJoinCols{
		String tabName;
		List<String> cols;
		tableJoinCols(String t,List<String> l){
			this.tabName = t;
			this.cols = l;
		}
	}
	static int createTableCounter = 0;
	static List<String> orderElements;
	static String precomputedorderpath = "";
	static boolean isNotPrecomputedorder = false;
	static boolean isLimitbreaks = false;
	static Map<String,Integer> indexdatamap;
	static int indexstart =-1;
	static String indexend ="";
	static String indexname;
	static boolean isOnlyWhere = false;
	static String indexsortedpath;
	static Map<String,String> precomputeValues = new HashMap<String,String>();
	static boolean isPrecomputedQuery = false;
	static StringBuffer precomputeStringBuffer ;
	static boolean joinFlag = false;
	static Map<String,ArrayList<Expression>> tableWhere = new HashMap<String,ArrayList<Expression>>();
	static ArrayList<JoinPair> joinPairList = new ArrayList<JoinPair>();
	static Map<String,colDataType> joinTableSchema = new HashMap<String,colDataType>();
	static Map<String,Set<String>> joinColumns = new HashMap<String,Set<String>>();
	static Map<String,List<Datatypes>> tableDatatypes = new HashMap<String,List<Datatypes>>();
	static List<toSortTableData> toSortTables= new ArrayList<toSortTableData>();
	static String groupKey ="";
	static Map<String,Expression> aliasMapping = new HashMap<String,Expression>();
	static Map<Expression,PrimitiveValue> columnExp = new HashMap<Expression,PrimitiveValue>();
	static List<tableJoinCols> orderJoinCols = new ArrayList<tableJoinCols>();
	static String newTablePath ="";
	static String dataPath="data/";
	static Map<String,Set<String>> referenceMap = new HashMap<String,Set<String>>();
	
	static List<tableLength> tableSizes = new ArrayList<tableLength>();
	
	public static void evaluateOnDisk() throws SQLException, IOException {

		Scanner scanner = new Scanner(System.in);

		while (true) {
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
					File dir = new File("data");
					if(createTableCounter==0){
						for(File file: dir.listFiles()){
							if (file.isDirectory()){
								  Main.Delete(file);
							}      
						}
					}
				
					    
					
					columnInfo(columns, cmap,table.getTable().getName());
					
					//Main.map.put(table.getTable().getName(), cmap);
					
					Main.mainDirNum = 10000;
					String tempPath = dataPath;
					int t = Main.mainDirNum;
					while (true) {
						String dirPath = tempPath + Integer.toString(t);
						File index = new File(dirPath);

						if (index.exists()) {
							Main.Delete(index);
						} else {
							break;
						}
						t++;
					}

					ExternalSort.directoryNum = 1;

					t = 1;
					while (true) {
						String dirPath = tempPath + Integer.toString(t);
						File index = new File(dirPath);

						if (index.exists()) {
							Main.Delete(index);
						} else {
							break;
						}
						t++;
					}
					
					String dirPath = dataPath+"Join";
					File index = new File(dirPath);

					if (index.exists()) {
						Main.Delete(index);
						ExternalJoin.JoinCount=1000;
					}
					dirPath = dataPath+"GroupAndOrder";
					index = new File(dirPath);
					if(index.exists()){
						Main.Delete(index);
					}
					
					if(createTableCounter==0){
						dirPath = dataPath+"sortedTables";
						index = new File(dirPath);

						if (index.exists()) {
							Main.Delete(index);
						}
					}
					String joinPath=dataPath+"Join_";
					int joinIndex = 0;
					while(true){
					//	System.out.println("joinPath "+joinPath+Integer.toString(joinIndex));
						File joinFile = new File(joinPath+Integer.toString(joinIndex)+".csv");
						if(joinFile.exists()){
						//	System.out.println("deleting "+joinPath+Integer.toString(joinIndex));
							joinFile.delete();
						}
						else{
						//	System.out.println("not found "+joinPath+Integer.toString(joinIndex));
							break;
						}
						joinIndex++;
					}
					createTableCounter++;
				
					sortOnIndexes(table.getTable().getName(),table.getIndexes());
				//	System.err.println("OnDisk Create Table End");
				} else {
					System.err.println("OnDisk Select Query Start");
					selectStatements(statement);
					System.err.println("OnDisk Select Query end");
				}
			} catch (ParseException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}

	public static void selectStatements(Statement statement) throws SQLException {
		//System.out.println("debugging1");
		
		Main.clearGlobalVariables();
		Select select = (Select) statement;
		//System.err.println("Select Query "+select.toString());
		SelectBody body = select.getSelectBody();
		PlainSelect pSelect = (PlainSelect) body;
		List<SelectItem> selectItems = pSelect.getSelectItems();
		List<Expression> nestedWheres = new ArrayList<Expression>();
		Expression whereExp = pSelect.getWhere();
	//	System.out.println("debugging2");
		List<Column> groupByExpr = pSelect.getGroupByColumnReferences();
		List<OrderByElement> orderByElements = pSelect.getOrderByElements();
		Main.rowCount = -1;
		Main.limitcounter = 0;
		aliasMapping.clear();
		groupKey = "";
		if (pSelect.getLimit() != null)
			Main.rowCount = pSelect.getLimit().getRowCount();

		FromItem item = pSelect.getFromItem();
		List<Join> ljs= pSelect.getJoins();
		
		Table table = (Table) item;
		Main.tableName = table.getName();
		
		if(ljs != null){
			joinFlag = true;
			List<String> joinTables = new ArrayList<String>();
			
			joinTables.add(table.getName());
			for(Join j : ljs){
				Table t= (Table) j.getRightItem();
				joinTables.add(t.getName());
			}
			
			findWhereOnJoins(whereExp,joinTables);
			
			sortJoinPairs(joinTables);
			
			Iterator<SelectItem> iter = selectItems.iterator();
			
			while (iter.hasNext()) {
				SelectItem sitem = iter.next();
				if(sitem instanceof SelectExpressionItem){
					SelectExpressionItem sei = (SelectExpressionItem)sitem;
					Expression exp = sei.getExpression();
					if(exp instanceof Column){
						Column c = (Column)exp;
						Table tb = (Table)c.getTable();
						if(tb != null){
							if(joinColumns.containsKey(tb.getName())){
								Set<String> l = joinColumns.get(tb.getName());
								l.add(c.getColumnName());
								joinColumns.put(tb.getName(),l);
							}
							else{
								Set<String> l = new HashSet<String>();
								l.add(c.getColumnName());
								joinColumns.put(tb.getName(),l);
							}
						}
					
					}
					else if(exp instanceof Function){
						Function f = (Function)exp;
						
						ExpressionList expList = f.getParameters();
						if(expList != null){
							List<Expression> exps = expList.getExpressions();
							if(exps != null){
								Expression firstExp = exps.get(0);
								GetProjectionsFromAggregates(firstExp);
							}
						}
						
						
					}
					
				}
			}
			
			if(groupByExpr != null){
				for(Column c:groupByExpr){
					Table tb = (Table)c.getTable();
					if(joinColumns.containsKey(tb.getName())){
						Set<String> l = joinColumns.get(tb.getName());
						l.add(c.getColumnName());
						joinColumns.put(tb.getName(),l);
					}
					else{
						Set<String> l = new HashSet<String>();
						l.add(c.getColumnName());
						joinColumns.put(tb.getName(),l);
					}
				}
			}
			
			if(orderByElements != null){
				for(OrderByElement ord:orderByElements){
					Expression exp = ord.getExpression();
					if(exp instanceof Column){
						Column c = (Column)exp;
						Table tb = (Table)c.getTable();
						if(joinColumns.containsKey(tb.getName())){
							Set<String> l = joinColumns.get(tb.getName());
							l.add(c.getColumnName());
							joinColumns.put(tb.getName(),l);
						}
						else{
							Set<String> l = new HashSet<String>();
							l.add(c.getColumnName());
							joinColumns.put(tb.getName(),l);
						}
					}
				}
			}
			
			double t1 = (new Timestamp(System.currentTimeMillis())).getTime();
			if(joinTables.size()!=joinPairList.size()){
				Main.tableName = ExternalJoin.SortMergeJoin();
			}
			else{
				Main.tableName = ExternalJoin.SortMergeJoinOld();
			}
			double t2 = (new Timestamp(System.currentTimeMillis())).getTime();
			System.err.println("Time for Join "+(t2-t1));
			File joinedFile = new File(dataPath+Main.tableName+".csv");
			if(!joinedFile.exists()){
				return;
			}
			
			isNotPrecomputedorder=true;
			whereExp = null;
			
			
		//	return;
		}
		
		
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

		BufferedReader br=null;
		
		if (groupByExpr != null && !groupByExpr.isEmpty()) {
			Main.groupByFlag = true;
		}
		
		if (orderByElements != null && !orderByElements.isEmpty()) {
			Main.orderbyflag = false;
			if(groupByExpr != null && orderByElements.size() == groupByExpr.size()){
				for (int i = 0; i < orderByElements.size(); i++) {
					Column col = (Column) orderByElements.get(i).getExpression();
					String colName = col.getColumnName();
					if(!groupByExpr.get(i).getColumnName().equals(colName)){
						Main.orderbyflag = true;
						break;
					}
				}
				
			}
			else{
				Main.orderbyflag = true;
			}
				
		}
		

		Iterator<SelectItem> iter = selectItems.iterator();
		List<Expression> expressionList = new LinkedList<Expression>();
		while (iter.hasNext()) {
			SelectItem sitem = iter.next();
			if (sitem instanceof AllColumns) {
				Main.isStar = true;
				break;
			}
			
			Expression exp = ((SelectExpressionItem) sitem).getExpression();
			String aliasString = ((SelectExpressionItem)sitem).getAlias();
			if(aliasString!=null){
				aliasMapping.put(aliasString,exp);
			}
			expressionList.add(exp);
		}
		List<Expression> allWhereClauses = new ArrayList<Expression>();
		if(Main.nestedFlag == true){
			allWhereClauses = nestedWheres;
		}
		else if(whereExp != null){
			allWhereClauses.add(whereExp);
		}
		else{
			allWhereClauses = null;
		}
		boolean lineItemFlag = false;
		try {
			if (Main.groupByFlag) {
				ArrayList<Integer> colIndexes = new ArrayList<Integer>();
				ArrayList<Datatypes> colDataTypes = new ArrayList<Datatypes>();
				ArrayList<Boolean> colsort = new ArrayList<Boolean>();
				for (Column col : groupByExpr) {
					String colName = col.getColumnName();
					colIndexes.add(Main.map.get(Main.tableName).get(colName).firstKey());
					colDataTypes.add(Main.map.get(Main.tableName).get(colName).firstEntry().getValue());
					colsort.add(true);
				}
				newTablePath = ExternalSort.DoExternalSorting(dataPath + Main.tableName + ".csv",
						colIndexes, colDataTypes, colsort,"",allWhereClauses);
			
			} else if (Main.orderbyflag) {
				ArrayList<Integer> colIndexes = new ArrayList<Integer>();
				ArrayList<Datatypes> colDataTypes = new ArrayList<Datatypes>();
				ArrayList<Boolean> colsort = new ArrayList<Boolean>();
				for (int i = 0; i < orderByElements.size(); i++) {
					Column col = (Column) orderByElements.get(i).getExpression();
					String colName = col.getColumnName();
					colIndexes.add(Main.map.get(Main.tableName).get(colName).firstKey());
					colDataTypes.add(Main.map.get(Main.tableName).get(colName).firstEntry().getValue());
					colsort.add(orderByElements.get(i).isAsc());
				}
				newTablePath = ExternalSort.DoExternalSorting(dataPath + Main.tableName + ".csv",
						colIndexes, colDataTypes, colsort,"",allWhereClauses);
			}
			if (Main.groupByFlag || Main.orderbyflag)
				br = new BufferedReader(new FileReader(newTablePath));
			else{
				if(whereExp!=null){
				//	evalWhereExp(whereExp);
					isOnlyWhere = true;	
					br = new BufferedReader(new FileReader(dataPath + Main.tableName + ".csv"));
				}else
					br = new BufferedReader(new FileReader(dataPath + Main.tableName + ".csv"));
			}
			
			File newFile = null;
			FileWriter fwr = null;
			BufferedWriter bwr = null;
			String groupByPath="";
			if(Main.groupByFlag && Main.orderbyflag){
				
				String dirPath = dataPath + "GroupAndOrder";
				
				File dir = new File(dirPath);
				// attempt to create the directory here
				if (!dir.exists()) {
					dir.mkdir();
					}
				groupByPath = dirPath+"/"+Integer.toString(Main.mainDirNum);
				newFile = new File(groupByPath);
				if(newFile.exists()){
					newFile.delete();
				}
				try{
					newFile.createNewFile();
					fwr = new FileWriter(newFile);
					bwr = new BufferedWriter(fwr);
				}
				catch(Exception e){
					System.out.println("Exception in groupbyfile "+e);
				}
				Main.mainDirNum++;
			}
			
			String line = "";
			Main.sumExp = new LinkedHashMap<Expression, Double>();
			Main.maxExp = new LinkedHashMap<Expression, Double>();
			Main.minExp = new LinkedHashMap<Expression, Double>();
			Main.countAggregate = 0;
			while ((line = br.readLine()) != null) {

				if (isLimitbreaks)
					break;
				Main.vals = line.split("\\|");
				Main.valslist = new ArrayList<PrimitiveValue>();
				for (int i = 0; i < Main.vals.length; i++) {
					if (tableDatatypes.get(Main.tableName).get(i) == Datatypes.INT) {
						Main.valslist.add(new LongValue(Main.vals[i]));
					} else if (tableDatatypes.get(Main.tableName).get(i) == Datatypes.DECIMAL) {
						Main.valslist.add(new DoubleValue(Main.vals[i]));
					} else if (tableDatatypes.get(Main.tableName).get(i) == Datatypes.CHAR) {
						Main.valslist.add(new StringValue(Main.vals[i]));
					} else if (tableDatatypes.get(Main.tableName).get(i) == Datatypes.STRING) {
						Main.valslist.add(new StringValue(Main.vals[i]));
					} else if (tableDatatypes.get(Main.tableName).get(i) == Datatypes.DATE) {
						Main.valslist.add(new DateValue(Main.vals[i]));
					}
					else if(tableDatatypes.get(Main.tableName).get(i) == Datatypes.VARCHAR){
						Main.valslist.add(new StringValue(Main.vals[i]));
					}
				}
				
				if(isOnlyWhere){
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
					Iterator<Expression> expIter = expressionList.iterator();
					while (expIter.hasNext()) {
						Expression expr = expIter.next();
						if(expr instanceof Function){
							Main.aggregatesEvaluation(expr);
							Main.countAggregate++;
						}
						else if(expr instanceof Column){
							Column c = (Column)expr;
							int ind = Main.map.get(Main.tableName).get(c.getColumnName()).firstKey();
							System.out.print(Main.vals[ind]+"|");
						}
						else if(Main.isStar){
							System.out.print(line);
						}
					}
					if(!Main.isAggregateExpression){
						System.out.println();
						Main.limitcounter++;
						if(Main.limitcounter==Main.rowCount){
							isLimitbreaks = true;
							br.close();
							return;
						}
					}
				}
				
				else if(Main.groupByFlag && !Main.orderbyflag){
					if(lineItemFlag){
						if(!Main.evaluateWhere(Main.valslist, whereExp)){
							continue;
						}
					}
					if(!exclusiveGroupBy(groupByExpr,expressionList)){
						return;
					}
				}
				else if(Main.groupByFlag && Main.orderbyflag){
					if(!exclusiveGroupByORderBy(groupByExpr,expressionList,bwr)){
						return;
					}
				}
				else if(Main.orderbyflag){
					Iterator<Expression> expIter = expressionList.iterator();
					while (expIter.hasNext()) {
						Expression expr = expIter.next();
						if(expr instanceof Column){
							Column c = (Column)expr;
							int ind = Main.map.get(Main.tableName).get(c.getColumnName()).firstKey();
							System.out.print(Main.vals[ind]+"|");
						}
						else if(Main.isStar){
							System.out.print(line);
						}
					}
					System.out.println();
				}
				else{
					Iterator<Expression> expIter = expressionList.iterator();
					while (expIter.hasNext()) {
						Expression expr = expIter.next();
						if(expr instanceof Function){
							Main.aggregatesEvaluation(expr);
							Main.countAggregate++;
						}
						else if(expr instanceof Column){
							Column c = (Column)expr;
							int ind = Main.map.get(Main.tableName).get(c.getColumnName()).firstKey();
							System.out.print(Main.vals[ind]+"|");
						}
						else if(Main.isStar){
							System.out.print(line);
						}
					}
					if(!Main.isAggregateExpression){
						System.out.println();
						Main.limitcounter++;
						if(Main.limitcounter==Main.rowCount){
							isLimitbreaks = true;
							br.close();
							return;
						}
					}
				}
			}
			br.close();
			if (Main.isAggregateExpression && !Main.groupByFlag) {
				Main.printResults(expressionList);
				Main.isAggregateExpression = false;
			}
			if (Main.groupByFlag && !Main.orderbyflag) {
				if (Main.limitcounter != Main.rowCount) {
					printOnDiskResults(expressionList);
				}	
				Main.sumExp.clear();
				Main.maxExp.clear();
				Main.minExp.clear();
				columnExp.clear();
				Main.countAggregate = 0;
				Main.groupByFlag = false;
				Main.isAggregateExpression = false;
			} else if (Main.groupByFlag && Main.orderbyflag) {
				if (Main.limitcounter != Main.rowCount) {
					writeOnDiskResults(expressionList,bwr);
				}	
				
				Main.sumExp.clear();
				Main.maxExp.clear();
				Main.minExp.clear();
				columnExp.clear();
				Main.countAggregate = 0;
				
					bwr.close();
					
					ArrayList<Integer> colIndexes = new ArrayList<Integer>();
					ArrayList<Datatypes> colDataTypes = new ArrayList<Datatypes>();
					ArrayList<Boolean> colsort = new ArrayList<Boolean>();
					
					for(OrderByElement ord:orderByElements){
						Expression exp = ord.getExpression();
						int ind = expressionList.indexOf(exp);
						if(ind!=-1){
							Column c = (Column)exp;
							Datatypes dtype = Main.map.get(Main.tableName).get(c.getColumnName()).firstEntry().getValue();
							colDataTypes.add(dtype);
							colIndexes.add(ind);
							colsort.add(ord.isAsc());
							
						}
						else {
							ind = expressionList.indexOf(aliasMapping.get(exp.toString()));
							colIndexes.add(ind);
							colDataTypes.add(Datatypes.DECIMAL);
							colsort.add(ord.isAsc());
						}
					}
					
					String orderedPath = ExternalSort.DoExternalSorting(groupByPath, colIndexes, colDataTypes,
							colsort, "",null);
					
					br = new BufferedReader(new FileReader(orderedPath));
					
					while((line=br.readLine())!=null){
						System.out.println(line);
						Main.limitcounter++;
						if(Main.limitcounter==Main.rowCount){
							isLimitbreaks = true;
							br.close();
							return;
						}
					}
					br.close();
			}
			Main.orderbyflag = false;
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	
		
	}
	
	public static boolean exclusiveGroupBy(List<Column> groupByExpr, List<Expression> expressionList)
			throws SQLException {
		String currentGroupKey ="";
	
		for (Column col : groupByExpr) {
			int ind = Main.map.get(Main.tableName).get(col.getColumnName()).firstKey();
			currentGroupKey+=(Main.vals[ind]+"|");
		}
		if(groupKey.equals("") ||currentGroupKey.equals(groupKey) ){
			groupKey = currentGroupKey;
			if(!evaluateGroupByExp(expressionList)){
				return false;
			}
		}
		else{
			printOnDiskResults(expressionList);
			Main.sumExp.clear();
			Main.maxExp.clear();
			Main.minExp.clear();
			columnExp.clear();
			Main.countAggregate = 0;
			groupKey = currentGroupKey;
			Main.limitcounter++;
			if(Main.limitcounter==Main.rowCount){
				isLimitbreaks = true;
				return true;
			}
			if(!evaluateGroupByExp(expressionList)){
				return false;
			}
		}
		Main.countAggregate++;
		return true;
	}
	
	public static void sortJoinPairs(List<String> joinTables){
		int sz = joinTables.size();
		if(sz != joinPairList.size()){
			ArrayList<JoinPair> temp = new ArrayList<JoinPair>();
			
			for(tableLength tl:tableSizes){
				if(joinTables.contains(tl.tabName)){
						List<String> cols = new ArrayList<String>();
						Iterator<JoinPair> it = joinPairList.iterator();
						while(it.hasNext()){
							JoinPair jp = it.next();
							if(jp.table1.equals(tl.tabName) || jp.table2.equals(tl.tabName)){
								cols.add(jp.joinCol);
							}
						}
						tableJoinCols obj = new tableJoinCols(tl.tabName,cols);
						orderJoinCols.add(obj);
				}
			}
		
			if(sz == joinPairList.size()){
				String tName = orderJoinCols.get(sz-1).tabName;
				List<String> temp2 = orderJoinCols.get(sz-1).cols;
				temp2.add("SUPPKEY");
				tableJoinCols obj = new tableJoinCols(tName,temp2);
				orderJoinCols.set(sz-1, obj);
			}
		}
		
		else{
			ArrayList<JoinPair> temp = new ArrayList<JoinPair>();
			for(int i = 0 ; i < joinTables.size()-1 ; i++){
				String t1 = joinTables.get(i);
				String t2 = joinTables.get(i+1);
				String colName="";
				Iterator<JoinPair> it = joinPairList.iterator();
				while(it.hasNext()){
					JoinPair jp = it.next();
					if((jp.table1.equals(t1) && jp.table2.equals(t2))||
							(jp.table1.equals(t2) && jp.table2.equals(t1))){
						colName = jp.joinCol;
						it.remove();
					}
				}
				if(colName.equals("")){
					continue;
				}
				//System.out.println("col "+colName);
				JoinPair jp2 = new JoinPair(t1,t2,colName);
				temp.add(jp2);
			}
			for(JoinPair jp:joinPairList){
				temp.add(jp);
			}
			joinPairList.clear();
			joinPairList = temp;
			Collections.reverse(joinPairList);
		}
		
	}
	
	public static boolean evaluateGroupByExp(List<Expression> expressionList){
		try{
			Iterator<Expression> expIter = expressionList.iterator();
			while (expIter.hasNext()) {
				Expression expr = expIter.next();
				if(expr instanceof Column){
					Column c = (Column)expr;
					int ind = Main.map.get(Main.tableName).get(c.getColumnName()).firstKey();
					PrimitiveValue value = Main.valslist.get(ind);
					columnExp.put(expr,value);
				}
				else{
				//	System.out.println("Aggregates");
					Main.aggregatesEvaluation(expr);
				//	System.out.println("Outside Aggregates");
				}	
			}
			return true;
		}
		catch(Exception e){
			for(int i = 0; i < Main.valslist.size();i++){
				System.out.println("Main.valslist "+Main.valslist.get(i));
			}
			System.out.println("Exception in evaluateGroupByExp "+e);
			return false;
		}
		
	}
	
	public static void printOnDiskResults(List<Expression> expressionList) {

		Iterator<Expression> expIter = expressionList.iterator();
	//	System.out.println("hello");
		while (expIter.hasNext()) {
			Expression expr = expIter.next();
			if (expr instanceof Function) {
				Function cfunt = (Function) expr;
				if (cfunt.getName().equals("SUM")) {
					System.out.print(Main.sumExp.get(expr) + "|");
				} else if (cfunt.getName().equals("MAX")) {
					double max = Main.maxExp.get(expr);
					System.out.print(max + "|");
				} else if (cfunt.getName().equals("MIN")) {
					double min = Main.minExp.get(expr);
					System.out.print(min + "|");
				} else if (cfunt.getName().equals("AVG")) {
					double avg = Main.sumExp.get(expr) / Main.countAggregate;
					System.out.print(avg + "|");
				} else if (cfunt.getName().equals("COUNT")) {
					System.out.print(Main.countAggregate + "|");
				}
			}
			else if(expr instanceof Column){
				PrimitiveValue value = columnExp.get(expr);
				if(value instanceof LongValue){
					LongValue lv = (LongValue) value;
					System.out.print(lv.toString() + "|");
				}else if(value instanceof DoubleValue){
					DoubleValue dv = (DoubleValue) value;
					System.out.print(dv.toString() + "|");
				}else if(value instanceof StringValue){
					StringValue sv = (StringValue) value;
					System.out.print(sv.toString() + "|");	
				}else if(value instanceof DateValue){
					DateValue ddv = (DateValue) value;
					System.out.print(ddv.toString() + "|");	
				}	
				
			}
		}
		System.out.println();
	}
	
	
	public static boolean exclusiveGroupByORderBy(List<Column> groupByExpr, List<Expression> expressionList,BufferedWriter bwr)
			throws SQLException {
		String currentGroupKey ="";
	
		for (Column col : groupByExpr) {
			int ind = Main.map.get(Main.tableName).get(col.getColumnName()).firstKey();
			currentGroupKey+=(Main.vals[ind]+"|");
		}
		if(groupKey.equals("") ||currentGroupKey.equals(groupKey) ){
			groupKey = currentGroupKey;
			if(!evaluateGroupByExp(expressionList)){
				return false;
			}
		}
		else{
			writeOnDiskResults(expressionList,bwr);
			Main.sumExp.clear();
			Main.maxExp.clear();
			Main.minExp.clear();
			columnExp.clear();
			Main.countAggregate = 0;
			groupKey = currentGroupKey;
			if(!evaluateGroupByExp(expressionList)){
				return false;
			}
		}
		Main.countAggregate++;
		return true;
	}
	
	public static void writeOnDiskResults(List<Expression> expressionList,BufferedWriter bwr) {
		try{
			Iterator<Expression> expIter = expressionList.iterator();
			//	System.out.println("hello");
				String result = "";
				while (expIter.hasNext()) {
					Expression expr = expIter.next();
					if (expr instanceof Function) {
						Function cfunt = (Function) expr;
						if (cfunt.getName().equals("SUM")) {
							result+=(Main.sumExp.get(expr) + "|");
						} else if (cfunt.getName().equals("MAX")) {
							double max = Main.maxExp.get(expr);
							result+=(max + "|");
						} else if (cfunt.getName().equals("MIN")) {
							double min = Main.minExp.get(expr);
							result+=(min + "|");
						} else if (cfunt.getName().equals("AVG")) {
							double avg = Main.sumExp.get(expr) / Main.countAggregate;
							result+=(avg + "|");
						} else if (cfunt.getName().equals("COUNT")) {
							result+=(Main.countAggregate + "|");
						}
					}
					else if(expr instanceof Column){
						PrimitiveValue value = columnExp.get(expr);
						if(value instanceof LongValue){
							LongValue lv = (LongValue) value;
							result+=(lv.toString() + "|");
						}else if(value instanceof DoubleValue){
							DoubleValue dv = (DoubleValue) value;
							result+=(dv.toString() + "|");
						}else if(value instanceof StringValue){
							StringValue sv = (StringValue) value;
							result+=(sv.toString() + "|");
						}else if(value instanceof DateValue){
							DateValue ddv = (DateValue) value;
							result+=(ddv.toString() + "|");
						}	
						
					}
				}
				bwr.write(result+"\n");
		}
		catch(Exception e){
			System.out.println("Exception in writeOnDiskResults "+e);
		}
	}
	
	public static void GetProjectionsFromAggregates(Expression exps){
		if(exps instanceof CaseExpression){
			CaseExpression caseExp = (CaseExpression)exps;
			List<WhenClause> wClauses = caseExp.getWhenClauses();
			for(WhenClause w:wClauses){
				Expression whenExp = w.getWhenExpression();
				if(whenExp instanceof OrExpression){
					OrExpression orExp = (OrExpression) whenExp;
					Expression leftExp = orExp.getLeftExpression();
					Expression rightExp = orExp.getRightExpression();
					if(leftExp instanceof EqualsTo){
						EqualsTo equalToExp = (EqualsTo)leftExp;
						Expression lExp = equalToExp.getLeftExpression();
						Expression rExp = equalToExp.getRightExpression();
						if(lExp instanceof Column){
							Column c = (Column)lExp;
							Table t = (Table)c.getTable();
							String tableName = t.getName();
							String colName = c.getColumnName();
							if(joinColumns.containsKey(tableName)){
								Set<String> list = joinColumns.get(tableName);
								list.add(colName);
								joinColumns.put(tableName,list);
							}
							else{
								Set<String> list = new HashSet<String>();
								list.add(colName);
								joinColumns.put(tableName,list);
							}
						}
						if(rExp instanceof Column){
							Column c = (Column)rExp;
							Table t = (Table)c.getTable();
							String tableName = t.getName();
							String colName = c.getColumnName();
							if(joinColumns.containsKey(tableName)){
								Set<String> list = joinColumns.get(tableName);
								list.add(colName);
								joinColumns.put(tableName,list);
							}
							else{
								Set<String> list = new HashSet<String>();
								list.add(colName);
								joinColumns.put(tableName,list);
							}
						}
					}
					if(rightExp instanceof EqualsTo){
						EqualsTo equalToExp = (EqualsTo)rightExp;
						Expression lExp = equalToExp.getLeftExpression();
						Expression rExp = equalToExp.getRightExpression();
						if(lExp instanceof Column){
							Column c = (Column)lExp;
							Table t = (Table)c.getTable();
							String tableName = t.getName();
							String colName = c.getColumnName();
							if(joinColumns.containsKey(tableName)){
								Set<String> list = joinColumns.get(tableName);
								list.add(colName);
								joinColumns.put(tableName,list);
							}
							else{
								Set<String> list = new HashSet<String>();
								list.add(colName);
								joinColumns.put(tableName,list);
							}
						}
						if(rExp instanceof Column){
							Column c = (Column)rExp;
							Table t = (Table)c.getTable();
							String tableName = t.getName();
							String colName = c.getColumnName();
							if(joinColumns.containsKey(tableName)){
								Set<String> list = joinColumns.get(tableName);
								list.add(colName);
								joinColumns.put(tableName,list);
							}
							else{
								Set<String> list = new HashSet<String>();
								list.add(colName);
								joinColumns.put(tableName,list);
							}
						}
					
					}
				}
			//	System.out.println("dummy");
				
			}
		}
		else{
			while((exps instanceof Multiplication) || (exps instanceof Addition)
					|| (exps instanceof Subtraction)){
				Expression left=null;
				Expression right=null;
				Expression l = null;
				Expression r = null;
				if(exps instanceof Multiplication){
					Multiplication mul = (Multiplication)exps;
					left = mul.getLeftExpression();
					right = mul.getRightExpression();
				}
				else if(exps instanceof Addition){
					Addition add = (Addition)exps;
					left = add.getLeftExpression();
					right = add.getRightExpression();
				}
				else if(exps instanceof Subtraction){
					Subtraction sub = (Subtraction)exps;
					left = sub.getLeftExpression();
					right = sub.getRightExpression();
				}
				
				if(right instanceof Addition){
					Addition add = (Addition)right;
					l = add.getLeftExpression();
					r = add.getRightExpression();
				}
				else if(right instanceof Multiplication){
					Multiplication mul = (Multiplication)right;
					l = mul.getLeftExpression();
					r = mul.getRightExpression();
				}
				else if(right instanceof Subtraction){
					Subtraction sub = (Subtraction)right;
					l = sub.getLeftExpression();
					r = sub.getRightExpression();
				}
				else if(right instanceof Column){
					Column c = (Column)right;
					String colName = c.getColumnName();
					Table t = (Table)c.getTable();
					String tableName = t.getName();
					if(joinColumns.containsKey(tableName)){
						Set<String> list = joinColumns.get(tableName);
						list.add(colName);
						joinColumns.put(tableName,list);
					}
					else{
						Set<String> list = new HashSet<String>();
						list.add(colName);
						joinColumns.put(tableName,list);
					}
				}
				if(l!=null && l instanceof Column){
					Column c = (Column)l;
					String colName = c.getColumnName();
					Table t = (Table)c.getTable();
					String tableName = t.getName();
					if(joinColumns.containsKey(tableName)){
						Set<String> list = joinColumns.get(tableName);
						list.add(colName);
						joinColumns.put(tableName,list);
					}
					else{
						Set<String> list = new HashSet<String>();
						list.add(colName);
						joinColumns.put(tableName,list);
					}
				}
				if(r!=null && r instanceof Column){
					Column c = (Column)r;
					String colName = c.getColumnName();
					Table t = (Table)c.getTable();
					String tableName = t.getName();
					if(joinColumns.containsKey(tableName)){
						Set<String> list = joinColumns.get(tableName);
						list.add(colName);
						joinColumns.put(tableName,list);
					}
					else{
						Set<String> list = new HashSet<String>();
						list.add(colName);
						joinColumns.put(tableName,list);
					}
				}
				exps = left;
			}
			if(exps instanceof Column){
				Column c = (Column)exps;
				String colName = c.getColumnName();
				Table t = (Table)c.getTable();
				String tableName = t.getName();
				if(joinColumns.containsKey(tableName)){
					Set<String> list = joinColumns.get(tableName);
					list.add(colName);
					joinColumns.put(tableName,list);
				}
				else{
					Set<String> list = new HashSet<String>();
					list.add(colName);
					joinColumns.put(tableName,list);
				}
			}
		}
		
	}
	
	public static void evalWhereExp(Expression whereExp) {
		
		while(whereExp instanceof AndExpression){
			AndExpression expr = (AndExpression) whereExp;
			Expression left = expr.getLeftExpression();
			Expression right = expr.getRightExpression();
			evaluateExpression(right);
			whereExp = left;
		}
		evaluateExpression(whereExp);
	}

	public static void evaluateExpression(Expression expr) {
		
		if(expr instanceof GreaterThanEquals){
			GreaterThanEquals gte = (GreaterThanEquals) expr;
			Expression left = gte.getLeftExpression();
			if(left instanceof Column){
				Column col = (Column) left;
				if(col.getColumnName().equals(indexname)){
					Function funct = (Function) gte.getRightExpression();
					StringValue sv = (StringValue) funct.getParameters().getExpressions().get(0);
					if(indexdatamap.containsKey(sv.getValue())){
						indexstart = indexdatamap.get(sv.getValue());
					}else {
						for(Map.Entry<String, Integer> entry : indexdatamap.entrySet()){		
							if(entry.getKey().compareTo(sv.getValue())>=0){
								indexstart = entry.getValue();	
								break;
							}	
						}		
					}	
					return;
				}	
			}else 
				return;
		}else if(expr instanceof MinorThan){
			MinorThan mt = (MinorThan) expr;
			Expression left = mt.getLeftExpression();
			if(left instanceof Column){
				Column col = (Column) left;
				if(col.getColumnName().equals(indexname)){
					Function funct = (Function) mt.getRightExpression();
					StringValue sv = (StringValue) funct.getParameters().getExpressions().get(0);
					indexend = sv.getValue();
					return;
				}	
			}else 
				return;	
		}
		
	}

	public static void sortOnIndexes(String tableName, List<Index> indexes){
		try{
			ArrayList<String> indexList = new ArrayList<String>();
			String dirPath = dataPath+"sortedTables";
			File dir = new File(dirPath);
			// attempt to create the directory here
			dir.mkdir();
			Iterator<toSortTableData> it = toSortTables.iterator();
		//	System.out.println("Debugging1");
			while (it.hasNext()) {
				toSortTableData obj = it.next();
				File f1 = new File(dataPath+"sortedTables/"+obj.tName+"_"+obj.tCol);
			//	System.out.println("Debugging2");
				if(f1.exists()) { 
				    it.remove();
				    continue;
				}
				if(!Main.map.containsKey(obj.tName)){
					continue;
				}
			
				//System.out.println("Debugging3");
				String filePath = dataPath+"sortedTables/"+obj.tName+"_"+obj.tCol;
				int colVal = Main.map.get(obj.tName).get(obj.tCol).firstKey();
				Datatypes dtype =  Main.map.get(obj.tName).get(obj.tCol).get(colVal);
				ArrayList<Integer> colIndexes = new ArrayList<Integer>();
				colIndexes.add(colVal);
				ArrayList<Datatypes> colDataTypes = new ArrayList<Datatypes>();
				colDataTypes.add(dtype);
				List<Boolean> colSortType = new ArrayList<Boolean>();
				colSortType.add(true);
			//	System.out.println("Debugging4");
			//	File newFile = new File(filePath);
			//	newFile.createNewFile();
				ExternalSort.DoExternalSorting(dataPath+obj.tName+".csv",colIndexes,colDataTypes
						, colSortType,filePath,null);
			//	System.out.println("Debugging5");
				it.remove();
			//	System.out.println("Debugging6");
			}
			
		}catch(Exception e){
			System.out.println("Exception in sortOnIndexes "+e);
		}
		
	}
	
	public static void findWhereOnJoins(Expression whereExp,List<String> ljs){
		
		while (whereExp instanceof AndExpression) {
			AndExpression andex = (AndExpression) whereExp;
			Expression left = andex.getLeftExpression();
			Expression right = andex.getRightExpression();
			findTablesInWhere(right);
			whereExp = left;
		}
		findTablesInWhere(whereExp);
	}
	
	public static void findTablesInWhere(Expression right){
		if(right instanceof EqualsTo && 
				((EqualsTo) right).getLeftExpression() instanceof Column
				&& ((EqualsTo) right).getRightExpression() instanceof Column){
			EqualsTo e = (EqualsTo)right;
			Column c1 = (Column) e.getLeftExpression();
			Column c2 = (Column) e.getRightExpression();
			Table tab1 = (Table)c1.getTable();
			Table tab2 = (Table)c2.getTable();
			JoinPair obj = new JoinPair(tab1.getName(),tab2.getName(),c1.getColumnName());
			joinPairList.add(obj);
		}
		else if(right instanceof OrExpression){
			OrExpression orExp = (OrExpression)right;
			Expression exp1 = orExp.getLeftExpression();
			if(exp1 instanceof EqualsTo){
				EqualsTo leftExp = (EqualsTo)exp1;
				Expression lExp = leftExp.getLeftExpression();
				Expression rExp = leftExp.getRightExpression();
				String tabName ="";
				if(lExp instanceof Column){
					Column c = (Column)lExp;
					Table t = (Table)c.getTable();
					tabName = t.getName();
				}
				else if(rExp instanceof Column){
					Column c = (Column)rExp;
					Table t = (Table)c.getTable();
					tabName = t.getName();
				}
				
				if(tableWhere.containsKey(tabName)){
					ArrayList<Expression> temp = tableWhere.get(tabName);
					temp.add(right);
					tableWhere.put(tabName, temp);
				}
				else{
					ArrayList<Expression> temp = new ArrayList<Expression>();
					temp.add(right);
					tableWhere.put(tabName, temp);
				}
			}
		}
		else{
			String tabName="";
			if(right instanceof GreaterThan){
				GreaterThan gt = (GreaterThan) right;
				if (gt.getLeftExpression() instanceof Column){
					Column c = (Column) gt.getLeftExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
				else{
					Column c = (Column) gt.getRightExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
			}
			else if(right instanceof MinorThan){
				MinorThan mt = (MinorThan) right;
				if (mt.getLeftExpression() instanceof Column){
					Column c = (Column) mt.getLeftExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
				else{
					Column c = (Column) mt.getRightExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
				
			}
			else if(right instanceof MinorThanEquals){
				MinorThanEquals mte = (MinorThanEquals) right;
				if (mte.getLeftExpression() instanceof Column){
					Column c = (Column) mte.getLeftExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
				else{
					Column c = (Column) mte.getRightExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
			}
			else if(right instanceof GreaterThanEquals){
				GreaterThanEquals gte = (GreaterThanEquals) right;
				if (gte.getLeftExpression() instanceof Column){
					Column c = (Column) gte.getLeftExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
				else{
					Column c = (Column) gte.getRightExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
			}
			else if(right instanceof EqualsTo){
				EqualsTo gte = (EqualsTo) right;
				if (gte.getLeftExpression() instanceof Column){
					Column c = (Column) gte.getLeftExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
				else{
					Column c = (Column) gte.getRightExpression();
					Table tab = (Table)c.getTable();
					tabName = tab.getName();
				}
			}
			if(tableWhere.containsKey(tabName)){
				ArrayList<Expression> temp = tableWhere.get(tabName);
				temp.add(right);
				tableWhere.put(tabName, temp);
			}
			else{
				ArrayList<Expression> temp = new ArrayList<Expression>();
				temp.add(right);
				tableWhere.put(tabName, temp);
			}
		}
	}
	
	public static void main(String[] args) throws SQLException, IOException {

		OnDisk.evaluateOnDisk();

	}

	public static void columnInfo(List<ColumnDefinition> columns, Map<String, TreeMap<Integer, Datatypes>> cmap, String tableName) {
		List<Datatypes> dataTypeList = new ArrayList<Datatypes>();
		for (int i = 0; i < columns.size(); i++) {
			TreeMap<Integer, Datatypes> indexType = new TreeMap<Integer, Datatypes>();
			String dType = columns.get(i).getColDataType().getDataType();
			List<String> referenceColumns = columns.get(i).getColumnSpecStrings();
			
			joinColumns.put(tableName,referenceMap.get(tableName));
			for(String colName : referenceMap.get(tableName)){
				toSortTableData obj1 = new toSortTableData(tableName,colName);
				toSortTables.add(obj1);
			}
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
			Main.map.put(tableName,cmap);
			dataTypeList.add(enumDataType);
		}
		tableDatatypes.put(tableName, dataTypeList);
	}

}
