package dubstep;

import java.sql.SQLException;

import net.sf.jsqlparser.eval.Eval;
import net.sf.jsqlparser.expression.DateValue;
import net.sf.jsqlparser.expression.DoubleValue;
import net.sf.jsqlparser.expression.LongValue;
import net.sf.jsqlparser.expression.PrimitiveValue;
import net.sf.jsqlparser.expression.StringValue;
import net.sf.jsqlparser.schema.Column;

public class Evaluate extends Eval{

	@Override
	public PrimitiveValue eval(Column col) throws SQLException {
		
		int indexcol =Main.map.get(Main.tableName).get(col.getColumnName()).firstKey();
		PrimitiveValue value = Main.valslist.get(indexcol);
		if(value instanceof LongValue){
			return (LongValue) value;
		}else if(value instanceof DoubleValue){
			return (DoubleValue) value;
		}else if(value instanceof DateValue){
			return (DateValue) value;
		}else if(value instanceof StringValue){
			return (StringValue) value;
		}
		return null;
	}

}