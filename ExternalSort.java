package dubstep;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.PriorityQueue;

import dubstep.Main.Datatypes;
import net.sf.jsqlparser.expression.DateValue;
import net.sf.jsqlparser.expression.DoubleValue;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.expression.LongValue;
import net.sf.jsqlparser.expression.PrimitiveValue;
import net.sf.jsqlparser.expression.StringValue;

public class ExternalSort {
	static ArrayList<Integer> sortColIndexes = new ArrayList<Integer>();
	static ArrayList<Datatypes> sortColDataTypes = new ArrayList<Datatypes>();
	static List<Boolean> sortType = new ArrayList<Boolean>();
	static int directoryNum = 1;

	public static class kSort {
		int index;
		String str;

		kSort(int ind, String str) {
			this.index = ind;
			this.str = str;
		}
	}

	public static class sortMultipleColumnsComparator implements Comparator<String> {

		public int compare(String m1, String m2) {

			String[] values1;
			String[] values2;
			values1 = m1.split("\\|");
			values2 = m2.split("\\|");
			// System.out.println("values1 "+m1);
			// System.out.println("values2 "+m2);

			int i = 0;
			int sz = sortColIndexes.size();
			// int sComp=0;
			while (i < sz) {
				Datatypes dataType = sortColDataTypes.get(i);
				int res = 0;
				String s1 = values1[sortColIndexes.get(i)];
				String s2 = values2[sortColIndexes.get(i)];
				if (dataType == Datatypes.INT) {
					res = Integer.parseInt(s1) - Integer.parseInt(s2);
					// System.out.println("S1, S2 "+s1+","+s2+" "+res);
				} else if (dataType == Datatypes.DECIMAL) {
					if (Double.parseDouble(s1) - Double.parseDouble(s2) > 0) {
						res = 1;
					} else if (Double.parseDouble(s1) - Double.parseDouble(s2) < 0) {
						res = -1;
					}
				} else if (dataType == Datatypes.VARCHAR) {
					res = s1.compareTo(s2);
				} else if (dataType == Datatypes.CHAR) {
					res = s1.compareTo(s2);
				} else if (dataType == Datatypes.STRING) {
					res = s1.compareTo(s2);
				} else if (dataType == Datatypes.DATE) {
					res = s1.compareTo(s2);
				}
				if (res != 0) {
					if (sortType.get(i) == true) {
						return res;
					}
					return -res;
				}
				i++;
			}
			return 0;
		}
	}
	
	
	public static class muliplecolscomppv implements Comparator<List<PrimitiveValue>>{

		   public int compare(List<PrimitiveValue> list1, List<PrimitiveValue> list2){
	    		
	    		int i = 0;
	    		int sz = sortColIndexes.size();
	    		while(i<sz)
	    		{
	    			Datatypes dataType = sortColDataTypes.get(i);
	    			int res = 0;
	    			PrimitiveValue s1 = list1.get(sortColIndexes.get(i));
	    			PrimitiveValue s2 = list2.get(sortColIndexes.get(i));
	    			if(dataType == Datatypes.INT)
					{
	    				LongValue ls1 = (LongValue) s1;
	    				LongValue ls2 = (LongValue) s2;
	    				if(ls1.toLong() - ls2.toLong()>0){
	    					res =1;
	    				}else if(ls1.toLong() - ls2.toLong()<0)
	    					res =-1;
					}
	    			else if(dataType == Datatypes.DECIMAL)
					{
	    				DoubleValue ds1 = (DoubleValue) s1;
	    				DoubleValue ds2 = (DoubleValue) s2;
						if(ds1.toDouble()-ds2.toDouble()>0)
						{
							res = 1;
						}
						else if(ds1.toDouble()-ds2.toDouble()<0)
						{
							res = -1;
						}
					}
	    			else if(dataType == Datatypes.VARCHAR)
					{
	    				StringValue ss1 = (StringValue) s1;
	    				StringValue ss2 = (StringValue) s2;
	    				res = ss1.getValue().compareTo(ss2.getValue());

					}
	    			else if(dataType == Datatypes.CHAR)
					{
	    				StringValue ss1 = (StringValue) s1;
	    				StringValue ss2 = (StringValue) s2;
	    				res = ss1.getValue().compareTo(ss2.getValue());
					}
	    			else if(dataType == Datatypes.STRING)
					{
	    				StringValue ss1 = (StringValue) s1;
	    				StringValue ss2 = (StringValue) s2;
	    				res = ss1.getValue().compareTo(ss2.getValue());
					}
	    			else if(dataType == Datatypes.DATE)
					{
	    				DateValue ds1 = (DateValue) s1;
	    				DateValue ds2 = (DateValue) s2;
	    				res = ds1.toString().compareTo(ds2.toString());
					}
	    			if(res!=0)
					{
						if(sortType.get(i)==true)
						{
							return res;
						}
						return -res;
					}
	    			i++;
	    		}
	    		return 0;	
	        }		
	}

	public static String DoExternalSorting(String filePath, ArrayList<Integer> colIndexes,
			ArrayList<Datatypes> colDataTypes, List<Boolean> colSortType,
			String finalPath,List<Expression> whereClauses) {
		try {
			int chunkSize = 100000;
			BufferedReader br;
			sortColIndexes = colIndexes;
			sortColDataTypes = colDataTypes;
			sortType = colSortType;
			int index = filePath.lastIndexOf("/");
			String dirPath = filePath.substring(0, index);
			{
				// return filePath;
			}

			br = new BufferedReader(new FileReader(filePath));
			// System.out.println("DoExternalSorting Started ");
			File dir = new File(dirPath + "/" + Integer.toString(directoryNum));
			// attempt to create the directory here
			boolean successful = dir.mkdir();
			if (successful) {
				// System.out.println("Directory successfully created ");
			}
			String line = "";
			int count = 0;
			ArrayList<String> chunk = new ArrayList<String>();

			int chunkNum = 1;
			dirPath += "/";
			dirPath += Integer.toString(directoryNum);
			dirPath += "/";
			
			if(whereClauses == null){
				while ((line = br.readLine()) != null) {

					if (count < chunkSize) {
						chunk.add(line);
						count++;
					} else {
						Collections.sort(chunk, new sortMultipleColumnsComparator());
						String newFilePath = dirPath;
						newFilePath += "_1_";
						newFilePath += Integer.toString(chunkNum);
						CreateFileAndDumpData(chunk, newFilePath);
						chunkNum++;
						count = 1;
						chunk.clear();
						chunk.add(line);
					}

				}
			}
			else{
				while ((line = br.readLine()) != null) {
					if(!IsWhereClauseSatisfied(line,whereClauses,OnDisk.tableDatatypes.get(Main.tableName))){
						continue;
					}
					if (count < chunkSize) {
						chunk.add(line);
						count++;
					} else {
						Collections.sort(chunk, new sortMultipleColumnsComparator());
						String newFilePath = dirPath;
						newFilePath += "_1_";
						newFilePath += Integer.toString(chunkNum);
						CreateFileAndDumpData(chunk, newFilePath);
						chunkNum++;
						count = 1;
						chunk.clear();
						chunk.add(line);
					}

				}
			}
			
			// System.out.println("Chunkcount :"+chunkNum);
			if (count > 0) {
				Collections.sort(chunk, new sortMultipleColumnsComparator());
				
				String newFilePath = "";
				if(chunkNum == 1 && !finalPath.equals("")){
					newFilePath = finalPath;
				}
				else{
					newFilePath = dirPath;
					newFilePath += "_1_";
					newFilePath += Integer.toString(chunkNum);
				}
				CreateFileAndDumpData(chunk, newFilePath);
				chunk.clear();
			}
			String finalSortedFile = dirPath + "_1_1";
			// System.out.println("dirPath "+dirPath);
			br.close();
			// return dirPath+"_1_"+Integer.toString(chunkNum);

			if (chunkNum > 1) {

				finalSortedFile = SortAndMerge(dirPath, chunkNum, chunkSize,finalPath);
			}
			// System.out.println("finalSortedFile :"+finalSortedFile);

			directoryNum++;
			return finalSortedFile;
		} catch (Exception e) {
			System.out.println("Exception :" + e);
			return "";
		}

	}
	
	static boolean IsWhereClauseSatisfied(String line,List<Expression> whereExp,List<Datatypes> dtype){
		try{
			String[] splitLine = line.split("\\|");
			Main.vals = splitLine;
			
			Main.valslist = new ArrayList<PrimitiveValue>();
			for (int i = 0; i < Main.vals.length; i++) {
				if (dtype.get(i) == Datatypes.INT) {
					Main.valslist.add(new LongValue(Main.vals[i]));
				} else if (dtype.get(i) == Datatypes.DECIMAL) {
					Main.valslist.add(new DoubleValue(Main.vals[i]));
				} else if (dtype.get(i) == Datatypes.CHAR) {
					Main.valslist.add(new StringValue(Main.vals[i]));
				} else if (dtype.get(i) == Datatypes.STRING) {
					Main.valslist.add(new StringValue(Main.vals[i]));
				} else if (dtype.get(i) == Datatypes.DATE) {
					Main.valslist.add(new DateValue(Main.vals[i]));
				}
				else if (dtype.get(i) == Datatypes.VARCHAR) {
					Main.valslist.add(new StringValue(Main.vals[i]));
				}
			}
		
			for(Expression expr: whereExp){
				if(!Main.evaluateWhere(Main.valslist, expr)){
					return false;
				}
			}
			return true;
		}
		catch(Exception e){
			System.out.println("Exception in Where Clause "+e);
			return false;
		}
		
	}
	static void CreateFileAndDumpData(ArrayList<String> data, String filePath) {
		try {
			FileWriter fwr = null;
			BufferedWriter bwr = null;
			File newFile = new File(filePath);
			if (newFile.exists()) {
				/// System.out.println("File already present "+filePath);
				fwr = new FileWriter(newFile, true);
			} else {
				// System.out.println("Creating new file "+filePath);
				newFile.createNewFile();
				fwr = new FileWriter(newFile);
			}

			bwr = new BufferedWriter(fwr);
			for (String row : data) {
				bwr.write(row + "\n");
			}
			bwr.close();
			fwr.close();
		} catch (Exception e) {
			System.out.println("CreateFileAndDumpData :" + e);
		}

	}

	static String SortAndMerge(String filePath, int chunkCount, int chunkSize,String sortedPath) {

		try {
			int phaseNum = 1;
			int k = chunkCount;

			// System.out.println("SortAndMerge started
			// "+chunkCount+","+chunkSize);

			String finalPath = "";
			if(sortedPath.equals("")){
				finalPath=filePath;
				finalPath += "_final";
			}
			else{
				finalPath = sortedPath;
			}
		//	System.out.println("final path is "+finalPath);
			File newFile = new File(finalPath);
		
			// System.out.println("finalPath "+finalPath);
			newFile.createNewFile();
			FileWriter fwr = new FileWriter(newFile);
			BufferedWriter bwr = new BufferedWriter(fwr);

			String file = "";
			BufferedReader[] br = new BufferedReader[k];
			for (int i = 0; i < k; i++) {
				file = filePath;
				file += "_";
				file += Integer.toString(phaseNum);
				file += "_";
				file += Integer.toString(i + 1);
				br[i] = new BufferedReader(new FileReader(file));
			}
			// System.out.println("All "+k+" files opened");
			Comparator<kSort> comparator = new KSortComparator();
			PriorityQueue<kSort> queue = new PriorityQueue<kSort>(k, comparator);

			for (int i = 0; i < k; i++) {
				String line = br[i].readLine();
				kSort obj = new kSort(i, line);
				queue.add(obj);
			}
			// System.out.println("Added initial lines to priority queue ");
			while (queue.size() != 0) {
				kSort sortedObj = queue.remove();
				String sortedString = sortedObj.str;
				int ind = sortedObj.index;

				bwr.write(sortedString + "\n");

				String nextLine = br[ind].readLine();
				if (nextLine != null) {
					kSort newObj = new kSort(ind, nextLine);
					queue.add(newObj);
				}
			}
			// System.out.println("Done merging");
			for (int i = 0; i < k; i++) {
				br[i].close();
			}

			bwr.close();
			fwr.close();
			return finalPath;

		} catch (Exception e) {
			System.out.println("Exception :" + e);
			return "";
		}

	}

	public static class KSortComparator implements Comparator<kSort> {

		public int compare(kSort k1, kSort k2) {
			String m1 = k1.str;
			String m2 = k2.str;
			int ind1 = k1.index;
			int ind2 = k2.index;
			String[] values1;
			String[] values2;
			values1 = m1.split("\\|");
			values2 = m2.split("\\|");
			// System.out.println("values1 "+m1);
			// System.out.println("values2 "+m2);

			int i = 0;
			int sz = sortColIndexes.size();
			// int sComp=0;
			while (i < sz) {
				Datatypes dataType = sortColDataTypes.get(i);
				int res = 0;
				String s1 = values1[sortColIndexes.get(i)];
				String s2 = values2[sortColIndexes.get(i)];
				if (dataType == Datatypes.INT) {
					res = Integer.parseInt(s1) - Integer.parseInt(s2);
					// System.out.println("S1, S2 "+s1+","+s2+" "+res);
				} else if (dataType == Datatypes.DECIMAL) {
					if (Double.parseDouble(s1) - Double.parseDouble(s2) > 0) {
						res = 1;
					} else if (Double.parseDouble(s1) - Double.parseDouble(s2) < 0) {
						res = -1;
					}
				} else if (dataType == Datatypes.VARCHAR) {
					res = s1.compareTo(s2);
				} else if (dataType == Datatypes.CHAR) {
					res = s1.compareTo(s2);
				} else if (dataType == Datatypes.STRING) {
					res = s1.compareTo(s2);
				} else if (dataType == Datatypes.DATE) {
					res = s1.compareTo(s2);
				}
				if (res != 0) {
					if (sortType.get(i) == true) {
						return res;
					}
					return -res;
				}
				i++;
			}

			if (ind1 > ind2) {
				return 1;
			} else if (ind1 < ind2) {
				return -1;
			}
			return 0;
		}
	}

}
