public class Counting {


	//@ ensures \result == (\num_of int i; 0<=i && i<a.length; a[i] == v);
	//@ pure
	public static int count(int[] a, int v) {
		int r = 0;
		int k = 0;
		//@ maintaining 0<=k && k<=a.length;
		//@ maintaining r == (\num_of int i; 0<=i && i<k; a[i] == v);
		//@ decreasing a.length-k;
		//@ assignable r;
		while (k!=a.length) {
			if (a[k]==v) { r = r+1; }
			k=k+1;
		}
		return r; 
	}

	//@ requires 0 <= m && m<=a.length;
	//@ ensures \result == (\num_of int i; 0<=i && i<m; a[i] == v);
	//@ ensures_redundantly m==0 ==> \result==0;
	//@ ensures_redundantly m > 0 && a[m-1]==v ==> \result == count_to(a,m-1,v)+1;
	//@ ensures_redundantly m > 0 && a[m-1]!=v ==> \result == count_to(a,m-1,v);
	//@ pure
	public static int count_to(int[] a, int m, int v) {
		int r = 0;
		//@ maintaining 0<=k && k<=m;
		//@ maintaining 0 <= r && r <= k;
		//@ maintaining r == (\num_of int i; 0<=i && i<k; a[i] == v);
		//@ decreasing m-k;
		//@ assignable r;
		for(int k=0; k!=m; k=k+1) {
			if (a[k]==v) { r = r+1; }
		}
		return r; 
	}
	
}
