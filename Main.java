package dubstep;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import net.sf.jsqlparser.expression.BooleanValue;
import net.sf.jsqlparser.expression.DateValue;
import net.sf.jsqlparser.expression.DoubleValue;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.expression.Function;
import net.sf.jsqlparser.expression.LongValue;
import net.sf.jsqlparser.expression.PrimitiveValue;
import net.sf.jsqlparser.expression.StringValue;
import net.sf.jsqlparser.expression.operators.relational.ExpressionList;
import net.sf.jsqlparser.schema.Column;

public class Main {
	static Map<String, Map<String, TreeMap<Integer, Datatypes>>> map = new HashMap<String, Map<String, TreeMap<Integer, Datatypes>>>();
	static String[] vals;
	static boolean isAggregateExpression = false;
	static Map<Expression, Double> sumExp;
	static Map<Expression, Double> maxExp;
	static Map<Expression, Double> minExp;
	static String tableName;
	static double maxAggregate = Double.MIN_VALUE;
	static double minAggregate = Double.MAX_VALUE;
	static int countAggregate = 0;
	static boolean groupByFlag = false;
	static TreeSet<String> groupByKeys = new TreeSet<String>();
	static String newtableName;
	static boolean orderbyflag = false;
	static StringBuffer orderByappend;
	static int chunkSize = 100000;
	static int chunkCounter = 0;
	static String orderfilepath = "";
	static String filterfilepath = "";
	static long limitcounter = 0;
	static long rowCount = -1;
	static int mainDirNum = 10000;
	static StringBuffer fsb = new StringBuffer();
	static boolean nestedFlag = false;
	static boolean isStar = false;
	static boolean isWhereOuts = false;
	static List<PrimitiveValue> valslist;
	static List<List<PrimitiveValue>> grouporderjoin = new ArrayList<List<PrimitiveValue>>();
	static List<PrimitiveValue> oldvalslist = new ArrayList<PrimitiveValue>();

	public enum Datatypes {
		INT, STRING, VARCHAR, CHAR, DECIMAL, DATE, UNKNOWN
	}

	public static void main(String[] args) throws SQLException, IOException {
		
		if (args[1].equals("--in-mem")) {
			System.out.println("In Mem");
		InMemory.evaluateInMem();
		}else{
				System.out.println("On Disk");
		OnDisk.evaluateOnDisk();
		}
		
	}

	public static void clearGlobalVariables() {
		isAggregateExpression = false;
		countAggregate = 0;
		groupByFlag = false;
		orderbyflag = false;
		groupByKeys = new TreeSet<String>();
		limitcounter = 0;
		rowCount = -1;
		fsb = new StringBuffer();
		chunkCounter = 0;
		isStar = false;
		nestedFlag = false;
		InMemory.isFull = false;
		InMemory.passIdxs = new LinkedHashSet<Long>();
		InMemory.isWhereNotPass = false;
		OnDisk.isNotPrecomputedorder = false;
		OnDisk.isLimitbreaks = false;
		OnDisk.isOnlyWhere =false;
		oldvalslist.clear();
		grouporderjoin.clear();
		InMemory.finalJoinIdxs.clear();
		InMemory.finalJoindatatypes.clear();
		InMemory.expressionidxs.clear();
		InMemory.expressiontypes.clear();
		OnDisk.joinPairList.clear();
		OnDisk.joinTableSchema.clear();
		OnDisk.joinFlag = false;
		OnDisk.columnExp.clear();
		OnDisk.tableWhere.clear();
		OnDisk.orderJoinCols.clear();
	}

	public static void writeToFile(String str) {

		try {
			FileWriter fwr = null;
			BufferedWriter bwr = null;
			File newFile = new File(filterfilepath);
			if (newFile.exists()) {
				// System.out.println("File already present "+filterfilepath);
				fwr = new FileWriter(newFile, true);
			} else {
				// System.out.println("Creating new file "+filterfilepath);
				newFile.createNewFile();
				fwr = new FileWriter(newFile);
			}

			bwr = new BufferedWriter(fwr);
			bwr.write(str);
			bwr.close();
			fwr.close();
		} catch (Exception e) {
			System.out.println("CreateFileAndDumpData :" + e);
		}
	}

	public static void Delete(File f) throws IOException {
		if (f.isDirectory()) {
			for (File c : f.listFiles()) {
				// System.out.println("Deleting file/directory "+c.getName());
				Delete(c);

			}

		}
		if (!f.delete())
			throw new FileNotFoundException("Failed to delete file: " + f);
	}

	public static void flushData(StringBuffer orderByappend) {

		try {
			FileWriter fwr = null;
			BufferedWriter bwr = null;
			File newFile = new File(orderfilepath);
			if (newFile.exists()) {
				// System.out.println("File already present "+orderfilepath);
				fwr = new FileWriter(newFile, true);
			} else {
				// System.out.println("Creating new file "+orderfilepath);
				newFile.createNewFile();
				fwr = new FileWriter(newFile);
			}

			bwr = new BufferedWriter(fwr);
			bwr.write(orderByappend.toString());
			bwr.close();
			fwr.close();
		} catch (Exception e) {
			System.out.println("CreateFileAndDumpData :" + e);
		}
	}

	public static void groupByOrderBy(List<Column> groupByExpr, List<Expression> expressionList, String res)
			throws SQLException {
		for (Column col : groupByExpr) {
			String colName = col.getColumnName();
			PrimitiveValue value = valslist.get(map.get(tableName).get(colName).firstKey());
			if(value instanceof LongValue){
				LongValue lv = (LongValue) value;
				res+=lv.toString()+"|";
			}else if(value instanceof DoubleValue){
				DoubleValue dv = (DoubleValue) value;
				res+= dv.toString()+"|";	
			}else if(value instanceof StringValue){
				StringValue sv = (StringValue) value;
				res+=sv.toString()+"|";			
			}else if(value instanceof DateValue){
				DateValue ddv = (DateValue) value;
				res+=ddv.toString()+"|";
			}
		}
		if (!groupByKeys.contains(res)) {
			if (groupByKeys.size() > 0) {
				orderByappend.append(groupByKeys.first());
				// System.out.print(groupByKeys.first());
				printResultsOrderBy(expressionList);
				sumExp.clear();
				maxExp.clear();
				minExp.clear();
				countAggregate = 0;
				groupByKeys.clear();
				chunkCounter++;
			}
			groupByKeys.add(res);
		}
		countAggregate++;
		Iterator<Expression> expIter = expressionList.iterator();
		// Evaluate evaluate = new Evaluate();
		while (expIter.hasNext()) {
			Expression expr = expIter.next();
			aggregatesEvaluation(expr);
		}
	}
	
	public static void groupByOrderByJoin(List<Column> groupByExpr, List<Expression> expressionList, String res)
			throws SQLException {
		for (Column col : groupByExpr) {
			String colName = col.getColumnName();
			PrimitiveValue value = valslist.get(map.get(tableName).get(colName).firstKey());
			if(value instanceof LongValue){
				LongValue lv = (LongValue) value;
				res+=lv.toString()+"|";
			}else if(value instanceof DoubleValue){
				DoubleValue dv = (DoubleValue) value;
				res+= dv.toString()+"|";	
			}else if(value instanceof StringValue){
				StringValue sv = (StringValue) value;
				res+=sv.toString()+"|";			
			}else if(value instanceof DateValue){
				DateValue ddv = (DateValue) value;
				res+=ddv.toString()+"|";
			}
		}
		if (!groupByKeys.contains(res)) {
			if (groupByKeys.size() > 0) {
				//orderByappend.append(groupByKeys.first());
				// System.out.print(groupByKeys.first());
				printResultsGroOrderByJoin(expressionList,Main.oldvalslist);
				sumExp.clear();
				maxExp.clear();
				minExp.clear();
				countAggregate = 0;
				groupByKeys.clear();
			}
			groupByKeys.add(res);
		}
		countAggregate++;
		Iterator<Expression> expIter = expressionList.iterator();
		// Evaluate evaluate = new Evaluate();
		while (expIter.hasNext()) {
			Expression expr = expIter.next();
			aggregatesEvaluation(expr);
		}
	}
	
	

	public static void printResultsGroOrderByJoin(List<Expression> expressionList,List<PrimitiveValue> validlist) {
		Iterator<Expression> expIter = expressionList.iterator();
		List<PrimitiveValue> goj = new ArrayList<PrimitiveValue>();
		while (expIter.hasNext()) {
			Expression expr = expIter.next();
			if (expr instanceof Function) {
				Function cfunt = (Function) expr;
				if (cfunt.getName().equals("SUM")) {
					goj.add(new DoubleValue(sumExp.get(expr)));
				} else if (cfunt.getName().equals("MAX")) {
					double max = maxExp.get(expr);
					goj.add(new DoubleValue(max));
				} else if (cfunt.getName().equals("MIN")) {
					double min = minExp.get(expr);
					goj.add(new DoubleValue(min));
				} else if (cfunt.getName().equals("AVG")) {
					double avg = sumExp.get(expr) / countAggregate;
					goj.add(new DoubleValue(avg));
				} else if (cfunt.getName().equals("COUNT")) {
					goj.add(new DoubleValue(countAggregate));
				}
			}else if(expr instanceof Column){		
				Column ccol = (Column) expr;
				PrimitiveValue val = validlist.get(map.get(tableName).get(ccol.getColumnName()).firstKey());
				goj.add(val);	
			}
		}
		grouporderjoin.add(goj);
	}

	public static void onlygroupby(List<Column> groupByExpr, List<Expression> expressionList, String res)
			throws SQLException {
		for (Column col : groupByExpr) {
			String colName = col.getColumnName();
			PrimitiveValue value = valslist.get(map.get(tableName).get(colName).firstKey());
			if(value instanceof LongValue){
				LongValue lv = (LongValue) value;
				res+=lv.toString()+"|";
			}else if(value instanceof DoubleValue){
				DoubleValue dv = (DoubleValue) value;
				res+= dv.toString()+"|";	
			}else if(value instanceof StringValue){
				StringValue sv = (StringValue) value;
				res+=sv.toString()+"|";			
			}else if(value instanceof DateValue){
				DateValue ddv = (DateValue) value;
				res+=ddv.toString()+"|";
			}	
		}
		if (!groupByKeys.contains(res)) {
			if (groupByKeys.size() > 0) {
				limitcounter++;
				System.out.print(groupByKeys.first());
				printResults(expressionList);
				sumExp.clear();
				maxExp.clear();
				minExp.clear();
				countAggregate = 0;
				groupByKeys.clear();
			}
			groupByKeys.add(res);
		}
		countAggregate++;

		Iterator<Expression> expIter = expressionList.iterator();
		while (expIter.hasNext()) {
			Expression expr = expIter.next();
			aggregatesEvaluation(expr);
		}
	}

	public static void aggregatesEvaluation(Expression expr) throws SQLException {
		isAggregateExpression = true;
		if (expr instanceof Function) {
			Function funct = (Function) expr;
			ExpressionList list = funct.getParameters();
			if (list != null) {
				List<Expression> exprs = list.getExpressions();
				if(funct.getName().equals("COUNT")){
					return;
				}
				if (funct.getName().equals("SUM")) {
					if (!sumExp.containsKey(expr)) {
						sumExp.put(expr, (double) 0);
					}
					sumFunction(expr, exprs);
				} else if (funct.getName().equals("MAX")) {
					if (!maxExp.containsKey(expr)) {
						maxExp.put(expr, Double.NEGATIVE_INFINITY);
					}
					maxAggregate(expr, exprs);
				} else if (funct.getName().equals("MIN")) {
					if (!minExp.containsKey(expr)) {
						minExp.put(expr, Double.POSITIVE_INFINITY);
					}
					minAggregate(expr, exprs);
				} else if (funct.getName().equals("AVG")) {
					if (!sumExp.containsKey(expr)) {
						sumExp.put(expr, (double) 0);
					}
					sumFunction(expr, exprs);
				}
			}
		}
	}

	public static void printResults(List<Expression> expressionList) {

		Iterator<Expression> expIter = expressionList.iterator();
		while (expIter.hasNext()) {
			Expression expr = expIter.next();
			if (expr instanceof Function) {
				Function cfunt = (Function) expr;
				if (cfunt.getName().equals("SUM")) {
					System.out.print(sumExp.get(expr) + "|");
				} else if (cfunt.getName().equals("MAX")) {
					double max = maxExp.get(expr);
					System.out.print(max + "|");
				} else if (cfunt.getName().equals("MIN")) {
					double min = minExp.get(expr);
					System.out.print(min + "|");
				} else if (cfunt.getName().equals("AVG")) {
					double avg = sumExp.get(expr) / countAggregate;
					System.out.print(avg + "|");
				} else if (cfunt.getName().equals("COUNT")) {
					System.out.print(countAggregate + "|");
				}
			}
		}
		System.out.println();
	}

	public static void printResultsOrderBy(List<Expression> expressionList) {
		Iterator<Expression> expIter = expressionList.iterator();
		while (expIter.hasNext()) {
			Expression expr = expIter.next();
			if (expr instanceof Function) {
				Function cfunt = (Function) expr;
				if (cfunt.getName().equals("SUM")) {
					orderByappend.append(sumExp.get(expr) + "|");
					// System.out.print(sumExp.get(expr) + "|");
				} else if (cfunt.getName().equals("MAX")) {
					double max = maxExp.get(expr);
					// System.out.print(max + "|");
					orderByappend.append(max + "|");
				} else if (cfunt.getName().equals("MIN")) {
					double min = minExp.get(expr);
					// System.out.print(min + "|");
					orderByappend.append(min + "|");
				} else if (cfunt.getName().equals("AVG")) {
					double avg = sumExp.get(expr) / countAggregate;
					// System.out.print(avg + "|");
					orderByappend.append(avg + "|");
				} else if (cfunt.getName().equals("COUNT")) {
					// System.out.print(countAggregate + "|");
					orderByappend.append(countAggregate + "|");
				}
			}
		}
		orderByappend.append(System.lineSeparator());
	}

	public static void minAggregate(Expression expr, List<Expression> list) throws SQLException {
		double locmin = 0;
		Iterator<Expression> itera = list.iterator();
		while (itera.hasNext()) {
			Expression curexp = itera.next();
			if (curexp instanceof Column) {
				locmin += columnSum(tableName, curexp);
			} else {
				locmin += expressionEval(tableName, curexp);
			}
		}
		locmin = Math.min(locmin, minExp.get(expr));
		minExp.put(expr, locmin);
	}

	public static void maxAggregate(Expression expr, List<Expression> list) throws SQLException {

		double locmax = 0;
		Iterator<Expression> itera = list.iterator();
		while (itera.hasNext()) {
			Expression curexp = itera.next();
			if (curexp instanceof Column) {
				locmax += columnSum(tableName, curexp);
			} else {
				locmax += expressionEval(tableName, curexp);
			}
		}
		locmax = Math.max(locmax, maxExp.get(expr));
		maxExp.put(expr, locmax);

	}

	public static void sumFunction(Expression expr, List<Expression> list) throws SQLException {
		double locsum = 0;
		Iterator<Expression> itera = list.iterator();
		while (itera.hasNext()) {
			Expression curexp = itera.next();
			if (curexp instanceof Column) {
				locsum += columnSum(tableName, curexp);
			} else {
				locsum += expressionEval(tableName, curexp);
			}
		}
		sumExp.put(expr, sumExp.get(expr) + locsum);
	}

	public static double columnSum(String tableName, Expression expr) {
		Column col = (Column) expr;
		PrimitiveValue val = valslist.get(map.get(tableName).get(col.getColumnName()).firstKey());
		if(val instanceof LongValue){
			LongValue lv = (LongValue) val;
			return lv.toDouble();
		}else if(val instanceof DoubleValue){
			DoubleValue dv = (DoubleValue) val;
			return dv.toDouble();
		}
		return 0;
	}
	
	public static String columnValue(String tableName, Expression expr){
		Column col = (Column) expr;
		PrimitiveValue val = valslist.get(map.get(tableName).get(col.getColumnName()).firstKey());
		if(val instanceof LongValue){
			LongValue lv = (LongValue) val;
			return lv.toString();
		}else if(val instanceof DoubleValue){
			DoubleValue dv = (DoubleValue) val;
			return dv.toString();
		}else if(val instanceof StringValue){
			StringValue sv= (StringValue) val;
			return sv.getValue();
		}else if(val instanceof DateValue){
			DateValue ddv = (DateValue) val;
			return ddv.toString();
		}
		return null;
	}

	public static double expressionEval(String tableName, Expression expr) throws SQLException {
		Evaluate evaluate = new Evaluate();
		PrimitiveValue res = evaluate.eval(expr);
		double value = 0;
		if (res instanceof LongValue) {
			LongValue result = (LongValue) res;
			value = result.toDouble();
		} else if (res instanceof DoubleValue) {
			DoubleValue result = (DoubleValue) res;
			value = result.toDouble();
		}
		return value;
	}

	public static boolean evaluateWhere(List<PrimitiveValue> valslist, Expression whereExp) throws SQLException {

		Evaluate evaluate = new Evaluate();
		PrimitiveValue result = evaluate.eval(whereExp);
		BooleanValue boolVal = (BooleanValue) result;
		return boolVal.getValue();
	}
}