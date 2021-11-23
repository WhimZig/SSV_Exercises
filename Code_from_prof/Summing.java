public class Summing {

	// The following FAILS, since JML for some reason does not simplify out the
	// terminal case of the loop in the postcondition
	//@ normal_behavior
	//@   requires a.length>=3;
	//@   ensures \result == (\sum int i; 0<=i && i<3; a[i]);
	//@   ensures \result == a[0]+a[1]+a[2];
	//@ pure
	public static int sum_first_three(int[] a) {
		int r=0;
		int k=0;
		//@ maintaining r == (\sum int i; 0<=i && i<k; a[i]);
		//@ maintaining 0<=k && k <= 3;
		//@ decreasing 3-k;
		//@ assignable r;
		while (k!=3) {
			r=r+a[k]; 
			k=k+1;
		}
		return r;
	}
	
	// pure
	//@ normal_behavior
	//@   requires 1<=m && m<= a.length;
	//@   ensures \result == (\sum int i; 0<=i && i<m; a[i]);
	public static int sum_to(int[] a, int m) {
		int r=0;
		int k=0;
		//@ maintaining 0<=k && k<=m;
		//@ maintaining r == (\sum int i; 0<=i && i<k; a[i]);
		//@ decreasing m-k;
		//@ assignable r;
		while (k!=m) {
			r=r+a[k];
			k=k+1;
		}
		return r; 
	}
	
	//@ normal_behavior
	//@   requires 0<=a.length;
	//@   ensures \result == (\sum int i; 0<=i && i<a.length; a[i]);
	//@ pure
	public static int sum(int[] a) {
		int r=0;
		int k=0;
		//@ maintaining 0<=k && k<=a.length;
		//@ maintaining r == (\sum int i; 0<=i && i<k; a[i]);
		//@ decreasing a.length-k;
		//@ assignable r;
		while (k!=a.length) {
			r=r+a[k];
			k=k+1;
		}
		return r; 
	}
	
	
	// Compute the sum of all integers from 0 up to (but not including) n
	//@ normal_behavior
	//@   requires 0<=n;
	//@   requires n<1000;
	//@   ensures \result * 2 == n*(n-1); 
	//@   ensures \result == (\sum int i; 0<=i && i<n; i); 
	//@   ensures_redundantly \result >=0;
	public static int sum_integers_to(int n) {
		int r=0;
		int k=0;
		//@ maintaining 0<=k && k<=n;
		//@ maintaining r*2 == k * (k-1);
		//@ maintaining r == (\sum int i; 0<=i && i<k; i); 
		//@ maintaining_redundantly r>=0;
		//@ decreasing n-k;
		//@ assignable r;
		while (k!=n) {
			r=r+k;
			k=k+1;
		}
		return r;
	}

}
