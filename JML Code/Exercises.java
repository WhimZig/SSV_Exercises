import java.util.ArrayList;

public class Exercises {

	public static boolean same_elements(int[] a, int[] b) {
		// First thing I can think off is sorting the two arrays internally and then just checking that
		// Second option I can think of is doing two array lists, one that contains count
		// 	and one that contains element. I'll do the second as it feels better for this
		
		// So first I create the arraylist for a, then I create the arraylist for b
		// I think there's a way of doing it at the same time? But fuck it, still O(n)
		if(a.length != b.length) {
			return false;
		}
		
		// I'll do three runs of the while loop
		// First round counts elements of a
		// Second counts elements of b
		// Third checks that count array is empty in total
		int k = 0;
		
		ArrayList<Integer> elements = new ArrayList<>();
		ArrayList<Integer> count = new ArrayList<>();
		
		boolean res = true;
		// First round
		while(k+1 < a.length) {
			
			int loc = elements.indexOf(a[k]);
			
			// This means the element isn't in the array, so we add it and increase the count by one
			if(loc == -1) {
				elements.add(a[k]);
				count.add(1);
			} else {
				count.set(loc, count.get(loc)+1);
			}
			k += 1;
		}
		
		k = 0;
		// Second round, checking if the elements exists
		while(k+1< b.length) {
			int loc = elements.indexOf(b[k]);
			
			if(loc == -1) {
				return false;
			} else {
				count.set(loc, count.get(loc)-1);
			}
			k += 1;
		}
		
		k = 0;
		
		// Third round, making sure that everything is zero
		while(k+1 < count.size()) {
			int val = count.get(k);
			if (val != 0) {
				return false;
			}
			
			k += 1;
		}
		
		return true;
		
	}

}
