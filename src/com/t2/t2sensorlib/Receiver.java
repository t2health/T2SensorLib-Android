package com.t2.t2sensorlib;

import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.net.ConnectivityManager;
import android.net.wifi.WifiManager;
import android.util.Log;

public class Receiver extends BroadcastReceiver {
	private static final String TAG = "BFDemo";	
	private static int lastWifiState = 0;
	private OnBioFeedbackMessageRecievedListener messageRecievedListener;
	
	public Receiver(OnBioFeedbackMessageRecievedListener omrl) {
		this.messageRecievedListener = omrl;
	}
	
	@Override
	public void onReceive(Context context, Intent intent) {
		String message = intent.getStringExtra("message");
		final String action = intent.getAction();	
		
		messageRecievedListener.onReceived(message);
	}


	public interface OnBioFeedbackMessageRecievedListener {
		public void onReceived(String message);
	}
	
}